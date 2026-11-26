import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Cascades.SingleTarget

/-!
# Sections 1, 2, & 5: Complete-Graph State Machine & Inductive Cascade Schedule

Formalizes the complete-graph multi-family cascade execution from `cascades.md`:
* Exact pool count `P = N(N-1)/2` (unequal families) and `P = Mm(Mm-1)/2` (equal families).
* Explicit complete-graph pool residual state and step-by-step validity predicate requiring
  every triangular trade to use pairwise distinct assets with **both support pools fair (`res = 0`)**.
* The explicit 4-stage schedule over all unordered family pairs `a < b`:
  1. External correction of original/original anchor `X_{a,0} X_{b,0}`.
  2. Original/wrapper targets `X_{a,i} X_{b,0}` via pivot `X_{a,0}`.
  3. Original/wrapper targets `X_{a,0} X_{b,j}` via pivot `X_{b,0}`.
  4. Wrapper/wrapper targets `X_{a,i} X_{b,j}` via pivot `X_{a,0}`.
* Machine-checked proofs of:
  * `cascadeSchedule_spec`: every step's support-fairness precondition holds inductively,
    every pool ends arbitrage-free (`res x y = 0`), `V = D ∑_{a<b} (5 m_a m_b - 4) |u_a - u_b|`,
    and `T = D ∑_{a<b} (4 m_a m_b - 2 m_a - 2 m_b) |u_a - u_b|`.
  * `cascadeSchedule_doubles_direct`: cascade taxable volume equals `2 ×` direct correction.
  * `equalFamily_boxed_formulas`: `V = (5 m^2 - 4) κ L S_M`, `T = 4 n(n+1) κ L S_M`,
    and `B₁ = 4 f κ L n(n+1) S_M`.
-/

namespace Cascades

section AssetsAndPools

/-- An asset in the multi-family universe: family index `a : Fin M` and intra-family index
`i : Fin (m a)`, where `i = 0` is the original asset and `i ≥ 1` are wrappers. -/
abbrev Asset {M : ℕ} (m : Fin M → ℕ) := Σ a : Fin M, Fin (m a)

/-- The original asset `X_{a,0}` of family `a`. -/
def orig {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a) (a : Fin M) : Asset m :=
  ⟨a, ⟨0, hm a⟩⟩

/-- Predicate identifying wrapped assets (`i ≠ 0`). -/
def isWrapped {M : ℕ} {m : Fin M → ℕ} (x : Asset m) : Bool :=
  x.2.val != 0

/-- Number of wrapped endpoints of a two-asset pool `{x, y}` (taxable transfers on external
correction, since originals are untaxed and mint/redemption legs are exempt). -/
def wrappedCount2 {M : ℕ} {m : Fin M → ℕ} (x y : Asset m) : ℕ :=
  (if isWrapped x then 1 else 0) + (if isWrapped y then 1 else 0)

/-- Number of wrapped vertices in a pool-to-pool triangle `(x, y, z)` (each shared transfer
around the cycle is counted once). -/
def wrappedCount3 {M : ℕ} {m : Fin M → ℕ} (x y z : Asset m) : ℕ :=
  (if isWrapped x then 1 else 0) + (if isWrapped y then 1 else 0) +
  (if isWrapped z then 1 else 0)

/-- Unordered pool (edge of the complete graph on all assets). -/
abbrev Pool {M : ℕ} (m : Fin M → ℕ) := { e : Sym2 (Asset m) // ¬ e.IsDiag }

/-- Total number of assets `N = ∑_a m_a`. -/
def totalAssets {M : ℕ} (m : Fin M → ℕ) : ℕ := ∑ a : Fin M, m a

theorem card_asset_eq {M : ℕ} (m : Fin M → ℕ) :
    Fintype.card (Asset m) = totalAssets m := by
  simp [Asset, totalAssets]

/-- Exact pool count of the complete graph: `P = N (N - 1) / 2`. -/
theorem card_pool_eq {M : ℕ} (m : Fin M → ℕ) :
    Fintype.card (Pool m) = totalAssets m * (totalAssets m - 1) / 2 := by
  have h1 : Fintype.card (Pool m) = (Fintype.card (Asset m)).choose 2 := by
    simpa [Pool] using Sym2.card_subtype_not_diag (α := Asset m)
  rw [h1, card_asset_eq, Nat.choose_two_right]

/-- Exact pool count for `M` equal-size families of size `m = n + 1`:
`P = M(n+1)(M(n+1) - 1) / 2`. -/
theorem card_pool_equal (M n : ℕ) :
    Fintype.card (Pool (fun _ : Fin M => n + 1)) =
      M * (n + 1) * (M * (n + 1) - 1) / 2 := by
  rw [card_pool_eq]
  simp [totalAssets]

end AssetsAndPools

section StateMachine

/-- Pool residual state + accumulated aggregate pool volume `vol` and taxable wrapped-transfer
volume `taxVol`. -/
structure GraphState {M : ℕ} (m : Fin M → ℕ) where
  res : Asset m → Asset m → ℝ
  vol : ℝ
  taxVol : ℝ

/-- Initial state after consistent external log-price shock vector `u : Fin M → ℝ`.
Every same-family pool starts fair (`u a - u a = 0`), and every cross-family pool between
families `a` and `b` starts with residual `u a - u b` (magnitude `ε_{ab} = |u a - u b|`). -/
def initState {M : ℕ} (m : Fin M → ℕ) (u : Fin M → ℝ) : GraphState m where
  res := fun x y => u x.1 - u y.1
  vol := 0
  taxVol := 0

/-- Clear the undirected edge `{x, y}` in a residual matrix, leaving all other edges untouched. -/
def clearEdge {M : ℕ} {m : Fin M → ℕ} (res : Asset m → Asset m → ℝ)
    (x y : Asset m) : Asset m → Asset m → ℝ :=
  fun p q => if (p = x ∧ q = y) ∨ (p = y ∧ q = x) then 0 else res p q

/-- Atomic execution operations in the schedule:
* `external x y`: externally correct pool `{x, y}` directly (1 leg, total size `D |r|`).
* `triangle x y pivot`: run the converged geometric sequence of optimal triangle trades
  `(x, y, pivot)` with external restoration of supports `{pivot, x}` and `{pivot, y}`
  after every round (proved in `SingleTarget.lean` to sum to `D |r|` per leg, i.e.,
  `5 D |r|` pool volume and `(wrappedCount3 x y pivot + wrappedCount2 pivot x + wrappedCount2 pivot y) D |r|`
  taxable wrapped volume, leaving `{x, y}` at `0` and both supports restored at `0`). -/
inductive Step {M : ℕ} (m : Fin M → ℕ)
  | external (x y : Asset m)
  | triangle (x y pivot : Asset m)

/-- Precondition for a step to be valid at state `st`:
* `external x y` requires distinct assets `x ≠ y`.
* `triangle x y pivot` requires pairwise distinct `x, y, pivot` AND both support pools
  `{pivot, x}` and `{pivot, y}` to be currently fair (`res = 0`). -/
def Step.valid {M : ℕ} {m : Fin M → ℕ} (st : GraphState m) : Step m → Prop
  | .external x y => x ≠ y
  | .triangle x y pivot =>
      x ≠ y ∧ x ≠ pivot ∧ y ≠ pivot ∧ st.res pivot x = 0 ∧ st.res pivot y = 0

/-- State transition produced by executing a single step. -/
def Step.apply {M : ℕ} {m : Fin M → ℕ} (D : ℝ) (st : GraphState m) : Step m → GraphState m
  | .external x y =>
      { res := clearEdge st.res x y
        vol := st.vol + D * |st.res x y|
        taxVol := st.taxVol + (wrappedCount2 x y : ℝ) * D * |st.res x y| }
  | .triangle x y pivot =>
      { res := clearEdge st.res x y
        vol := st.vol + 5 * D * |st.res x y|
        taxVol := st.taxVol +
          ((wrappedCount3 x y pivot + wrappedCount2 pivot x + wrappedCount2 pivot y : ℕ) : ℝ) *
            D * |st.res x y| }

/-- Inductive validity of a sequence of steps from starting state `st`. -/
def ValidTrace {M : ℕ} {m : Fin M → ℕ} (D : ℝ) : GraphState m → List (Step m) → Prop
  | _, [] => True
  | st, s :: ss => s.valid st ∧ ValidTrace D (s.apply D st) ss

/-- Execute a sequence of steps from starting state `st`. -/
def runSteps {M : ℕ} {m : Fin M → ℕ} (D : ℝ) : GraphState m → List (Step m) → GraphState m
  | st, [] => st
  | st, s :: ss => runSteps D (s.apply D st) ss

theorem runSteps_append {M : ℕ} {m : Fin M → ℕ} (D : ℝ) (st : GraphState m)
    (l₁ l₂ : List (Step m)) :
    runSteps D st (l₁ ++ l₂) = runSteps D (runSteps D st l₁) l₂ := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons s ss ih => exact ih (s.apply D st)

theorem validTrace_append {M : ℕ} {m : Fin M → ℕ} (D : ℝ) (st : GraphState m)
    (l₁ l₂ : List (Step m)) :
    ValidTrace D st (l₁ ++ l₂) ↔ ValidTrace D st l₁ ∧ ValidTrace D (runSteps D st l₁) l₂ := by
  induction l₁ generalizing st with
  | nil => simp [ValidTrace, runSteps]
  | cons s ss ih =>
    simp only [List.cons_append, ValidTrace, runSteps, ih]
    tauto

/-- When `pivot` is an original asset (`isWrapped pivot = false`), the triangle + two support
corrections generate exactly `2 * wrappedCount2 x y` taxable wrapped transfers per unit trade
— double the taxable volume of direct external correction. -/
theorem triangle_tax_multiplier_of_orig {M : ℕ} {m : Fin M → ℕ} (x y pivot : Asset m)
    (hp : isWrapped pivot = false) :
    wrappedCount3 x y pivot + wrappedCount2 pivot x + wrappedCount2 pivot y =
      2 * wrappedCount2 x y := by
  simp only [wrappedCount3, wrappedCount2, hp]
  cases isWrapped x <;> cases isWrapped y <;> decide

/-- Generic batch lemma for executing a duplicate-free list of directed cross-family targets
`targets` via a fixed pivot `pivot`, where every target has initial residual `r0` and
all supports `{pivot, x}` and `{pivot, y}` are already fair and disjoint from `targets`. -/
private theorem runTriangles_batch {M : ℕ} {m : Fin M → ℕ} (D r0 : ℝ)
    (pivot : Asset m) (st : GraphState m) (targets : List (Asset m × Asset m))
    (hnodup : targets.Nodup)
    (hcross : ∀ t ∈ targets, t.1.1 ≠ t.2.1)
    (hres : ∀ t ∈ targets, st.res t.1 t.2 = r0)
    (hpivot : ∀ t ∈ targets, t.1 ≠ pivot ∧ t.2 ≠ pivot ∧
      st.res pivot t.1 = 0 ∧ st.res pivot t.2 = 0)
    (hdisj_pair : ∀ t₁ ∈ targets, ∀ t₂ ∈ targets, ¬(t₁.1 = t₂.2 ∧ t₁.2 = t₂.1))
    (hdisj_sup : ∀ t₁ ∈ targets, ∀ t₂ ∈ targets,
      ¬((pivot = t₂.1 ∧ t₁.1 = t₂.2) ∨ (pivot = t₂.2 ∧ t₁.1 = t₂.1)) ∧
      ¬((pivot = t₂.1 ∧ t₁.2 = t₂.2) ∨ (pivot = t₂.2 ∧ t₁.2 = t₂.1))) :
    let steps := targets.map (fun t => Step.triangle t.1 t.2 pivot)
    let st' := runSteps D st steps
    ValidTrace D st steps ∧
    (∀ p q, st'.res p q =
      if ∃ t ∈ targets, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) then 0 else st.res p q) ∧
    st'.vol = st.vol + 5 * (targets.length : ℝ) * D * |r0| ∧
    st'.taxVol = st.taxVol +
      ((targets.map (fun t =>
        wrappedCount3 t.1 t.2 pivot + wrappedCount2 pivot t.1 + wrappedCount2 pivot t.2)).sum : ℝ) *
        D * |r0| := by
  induction targets generalizing st with
  | nil =>
    simp [ValidTrace, runSteps]
  | cons hd tl ih =>
    rcases List.nodup_cons.mp hnodup with ⟨hd_notin, tl_nodup⟩
    have hhd_mem : hd ∈ hd :: tl := List.mem_cons_self
    have hhd_cross : hd.1 ≠ hd.2 := fun h => hcross hd hhd_mem (congrArg Sigma.fst h)
    have hhd_piv := hpivot hd hhd_mem
    have hhd_valid : (Step.triangle hd.1 hd.2 pivot).valid st :=
      ⟨hhd_cross, hhd_piv.1, hhd_piv.2.1, hhd_piv.2.2.1, hhd_piv.2.2.2⟩
    set st1 := (Step.triangle hd.1 hd.2 pivot).apply D st
    have htl_res : ∀ t ∈ tl, st1.res t.1 t.2 = r0 := by
      intro t ht
      have ht_mem : t ∈ hd :: tl := List.mem_cons_of_mem hd ht
      simp only [st1, Step.apply, clearEdge]
      split_ifs with h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hd_notin (by cases t; cases hd; simp_all)
        · exact hdisj_pair t ht_mem hd hhd_mem ⟨h1, h2⟩
      · exact hres t ht_mem
    have htl_piv : ∀ t ∈ tl, t.1 ≠ pivot ∧ t.2 ≠ pivot ∧
        st1.res pivot t.1 = 0 ∧ st1.res pivot t.2 = 0 := by
      intro t ht
      have ht_mem : t ∈ hd :: tl := List.mem_cons_of_mem hd ht
      have hp := hpivot t ht_mem
      have hsup := hdisj_sup t ht_mem hd hhd_mem
      refine ⟨hp.1, hp.2.1, ?_, ?_⟩
      · simp only [st1, Step.apply, clearEdge, hsup.1, ↓reduceIte, hp.2.2.1]
      · simp only [st1, Step.apply, clearEdge, hsup.2, ↓reduceIte, hp.2.2.2]
    have hih := ih st1 tl_nodup
      (fun t ht => hcross t (List.mem_cons_of_mem hd ht))
      htl_res htl_piv
      (fun t₁ h1 t₂ h2 => hdisj_pair t₁ (List.mem_cons_of_mem hd h1) t₂ (List.mem_cons_of_mem hd h2))
      (fun t₁ h1 t₂ h2 => hdisj_sup t₁ (List.mem_cons_of_mem hd h1) t₂ (List.mem_cons_of_mem hd h2))
    rcases hih with ⟨hval_tl, hres_tl, hvol_tl, htax_tl⟩
    refine ⟨⟨hhd_valid, hval_tl⟩, ?_, ?_, ?_⟩
    · intro p q
      simp only [List.map_cons, runSteps]
      rw [hres_tl p q]
      simp only [st1, Step.apply, clearEdge, List.mem_cons, exists_eq_or_imp]
      by_cases h1 : ∃ t ∈ tl, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1)
      · simp [h1]
      · by_cases h2 : (p = hd.1 ∧ q = hd.2) ∨ (p = hd.2 ∧ q = hd.1)
        · simp [h1, h2]
        · simp [h1, h2]
    · simp only [List.map_cons, runSteps, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hvol_tl]
      simp only [st1, Step.apply, hres hd hhd_mem]
      ring
    · simp only [List.map_cons, runSteps, List.sum_cons]
      rw [htax_tl]
      simp only [st1, Step.apply, hres hd hhd_mem]
      push_cast
      ring

/-- Generic batch lemma for direct external correction of a duplicate-free list of cross-family
targets `(x, y)` with initial residual `r0`. -/
private theorem runExternals_batch {M : ℕ} {m : Fin M → ℕ} (D r0 : ℝ)
    (st : GraphState m) (targets : List (Asset m × Asset m))
    (hnodup : targets.Nodup)
    (hcross : ∀ t ∈ targets, t.1.1 ≠ t.2.1)
    (hres : ∀ t ∈ targets, st.res t.1 t.2 = r0)
    (hdisj_pair : ∀ t₁ ∈ targets, ∀ t₂ ∈ targets, ¬(t₁.1 = t₂.2 ∧ t₁.2 = t₂.1)) :
    let steps := targets.map (fun t => Step.external t.1 t.2)
    let st' := runSteps D st steps
    ValidTrace D st steps ∧
    (∀ p q, st'.res p q =
      if ∃ t ∈ targets, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) then 0 else st.res p q) ∧
    st'.vol = st.vol + (targets.length : ℝ) * D * |r0| ∧
    st'.taxVol = st.taxVol +
      ((targets.map (fun t => wrappedCount2 t.1 t.2)).sum : ℝ) * D * |r0| := by
  induction targets generalizing st with
  | nil => simp [ValidTrace, runSteps]
  | cons hd tl ih =>
    rcases List.nodup_cons.mp hnodup with ⟨hd_notin, tl_nodup⟩
    have hhd_mem : hd ∈ hd :: tl := List.mem_cons_self
    have hhd_valid : (Step.external hd.1 hd.2).valid st :=
      fun h => hcross hd hhd_mem (congrArg Sigma.fst h)
    set st1 := (Step.external hd.1 hd.2).apply D st
    have htl_res : ∀ t ∈ tl, st1.res t.1 t.2 = r0 := by
      intro t ht
      have ht_mem : t ∈ hd :: tl := List.mem_cons_of_mem hd ht
      simp only [st1, Step.apply, clearEdge]
      split_ifs with h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hd_notin (by cases t; cases hd; simp_all)
        · exact hdisj_pair t ht_mem hd hhd_mem ⟨h1, h2⟩
      · exact hres t ht_mem
    have hih := ih st1 tl_nodup
      (fun t ht => hcross t (List.mem_cons_of_mem hd ht))
      htl_res
      (fun t₁ h1 t₂ h2 => hdisj_pair t₁ (List.mem_cons_of_mem hd h1) t₂ (List.mem_cons_of_mem hd h2))
    rcases hih with ⟨hval_tl, hres_tl, hvol_tl, htax_tl⟩
    refine ⟨⟨hhd_valid, hval_tl⟩, ?_, ?_, ?_⟩
    · intro p q
      simp only [List.map_cons, runSteps]
      rw [hres_tl p q]
      simp only [st1, Step.apply, clearEdge, List.mem_cons, exists_eq_or_imp]
      by_cases h1 : ∃ t ∈ tl, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1)
      · simp [h1]
      · by_cases h2 : (p = hd.1 ∧ q = hd.2) ∨ (p = hd.2 ∧ q = hd.1)
        · simp [h1, h2]
        · simp [h1, h2]
    · simp only [List.map_cons, runSteps, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hvol_tl]
      simp only [st1, Step.apply, hres hd hhd_mem]
      ring
    · simp only [List.map_cons, runSteps, List.sum_cons]
      rw [htax_tl]
      simp only [st1, Step.apply, hres hd hhd_mem]
      push_cast
      ring

end StateMachine

section CompleteGraphSchedule

/-- All wrapped assets (`i ≥ 1`) in family `a`. -/
def familyWrappers {M : ℕ} (m : Fin M → ℕ) (a : Fin M) : List (Asset m) :=
  ((List.finRange (m a)).filter (fun i => i.val != 0)).map (fun i => ⟨a, i⟩)

/-- All assets in family `a`. -/
def familyAllAssets {M : ℕ} (m : Fin M → ℕ) (a : Fin M) : List (Asset m) :=
  (List.finRange (m a)).map (fun i => ⟨a, i⟩)

/-- Ordered list of all unordered family pairs `(a, b)` with `a < b`. -/
def unorderedPairList (M : ℕ) : List (Fin M × Fin M) :=
  (List.finRange M).flatMap (fun a =>
    ((List.finRange M).filter (fun b => decide (a < b))).map (fun b => (a, b)))

/-- Finite set of all unordered family pairs `(a, b)` with `a < b`. -/
def unorderedPairs (M : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- Total pairwise relative price shock `S_M = ∑_{a < b} |u_a - u_b|`. -/
def totalShock {M : ℕ} (u : Fin M → ℝ) : ℝ :=
  ∑ p ∈ unorderedPairs M, |u p.1 - u p.2|

private theorem mem_familyWrappers {M : ℕ} (m : Fin M → ℕ) (a : Fin M) (x : Asset m) :
    x ∈ familyWrappers m a ↔ x.1 = a ∧ x.2.val ≠ 0 := by
  simp only [familyWrappers, List.mem_map, List.mem_filter, List.mem_finRange, true_and, bne_iff_ne]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨rfl, hi⟩
  · rintro ⟨h1, h2⟩
    rcases x with ⟨a', i⟩
    dsimp at h1 h2
    subst h1
    exact ⟨i, h2, rfl⟩

private theorem familyWrappers_nodup {M : ℕ} (m : Fin M → ℕ) (a : Fin M) :
    (familyWrappers m a).Nodup := by
  unfold familyWrappers
  refine List.Nodup.map (fun i j h => ?_) ((List.nodup_finRange (m a)).filter _)
  simpa using h

private theorem familyWrappers_length {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a) (a : Fin M) :
    (familyWrappers m a).length = m a - 1 := by
  unfold familyWrappers
  rw [List.length_map]
  have hpos := hm a
  obtain ⟨k, hk⟩ : ∃ k, m a = k + 1 := ⟨m a - 1, by omega⟩
  rw [hk, List.finRange_succ, List.filter_cons]
  simp only [Fin.val_zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.filter_map,
    Function.comp_def]
  have hall : (List.finRange k).filter (fun i : Fin k => (Fin.succ i).val != 0) =
      List.finRange k := by
    rw [List.filter_eq_self]
    intro i _
    simp [Fin.val_succ]
  rw [hall, List.length_map, List.length_finRange]
  omega

/-- The explicit 4-stage cascade schedule for a single unordered family pair `(a, b)` with `a < b`:
1. External correction of original/original anchor `X_{a,0} X_{b,0}`.
2. Original/wrapper targets `X_{a,i} X_{b,0}` via pivot `X_{a,0}`.
3. Original/wrapper targets `X_{a,0} X_{b,j}` via pivot `X_{b,0}`.
4. Wrapper/wrapper targets `X_{a,i} X_{b,j}` via pivot `X_{a,0}`. -/
def pairSchedule {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a) (a b : Fin M) : List (Step m) :=
  [Step.external (orig m hm a) (orig m hm b)] ++
  ((familyWrappers m a).map (fun x => Step.triangle x (orig m hm b) (orig m hm a))) ++
  ((familyWrappers m b).map (fun y => Step.triangle (orig m hm a) y (orig m hm b))) ++
  (((familyWrappers m a).flatMap (fun x =>
      (familyWrappers m b).map (fun y => (x, y)))).map
    (fun t => Step.triangle t.1 t.2 (orig m hm a)))

/-- Direct-correction baseline schedule for a single unordered family pair `(a, b)`. -/
def pairDirectSchedule {M : ℕ} (m : Fin M → ℕ) (a b : Fin M) : List (Step m) :=
  ((familyAllAssets m a).flatMap (fun x =>
      (familyAllAssets m b).map (fun y => (x, y)))).map
    (fun t => Step.external t.1 t.2)

/-- Full complete-graph cascade schedule across all unordered family pairs `a < b`. -/
def cascadeSchedule {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a) : List (Step m) :=
  (unorderedPairList M).flatMap (fun p => pairSchedule m hm p.1 p.2)

/-- Full direct-correction baseline schedule across all unordered family pairs `a < b`. -/
def directSchedule {M : ℕ} (m : Fin M → ℕ) : List (Step m) :=
  (unorderedPairList M).flatMap (fun p => pairDirectSchedule m p.1 p.2)

private theorem pairSchedule_spec {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    (u : Fin M → ℝ) (D : ℝ) (a b : Fin M) (hab : a ≠ b) (st : GraphState m)
    (h_same_a : ∀ x : Asset m, x.1 = a → st.res (orig m hm a) x = 0)
    (h_same_b : ∀ y : Asset m, y.1 = b → st.res (orig m hm b) y = 0)
    (h_ab : ∀ x y : Asset m, x.1 = a → y.1 = b → st.res x y = u a - u b) :
    let st' := runSteps D st (pairSchedule m hm a b)
    ValidTrace D st (pairSchedule m hm a b) ∧
    (∀ p q, st'.res p q =
      if (p.1 = a ∧ q.1 = b) ∨ (p.1 = b ∧ q.1 = a) then 0 else st.res p q) ∧
    st'.vol = st.vol + (5 * (m a : ℝ) * (m b : ℝ) - 4) * D * |u a - u b| ∧
    st'.taxVol = st.taxVol +
      (4 * (m a : ℝ) * (m b : ℝ) - 2 * (m a : ℝ) - 2 * (m b : ℝ)) * D * |u a - u b| := by
  have hma_pos : 1 ≤ m a := hm a
  have hmb_pos : 1 ≤ m b := hm b
  -- Stage 1: anchor X_{a,0} X_{b,0}
  set oa := orig m hm a
  set ob := orig m hm b
  have hoa_ne_ob : oa ≠ ob := fun h => hab (congrArg Sigma.fst h)
  have h1_valid : ValidTrace D st [Step.external oa ob] := ⟨hoa_ne_ob, trivial⟩
  set st1 := runSteps D st [Step.external oa ob]
  have hst1_res : ∀ p q, st1.res p q = clearEdge st.res oa ob p q := fun _ _ => rfl
  have hst1_vol : st1.vol = st.vol + D * |u a - u b| := by
    simp only [st1, runSteps, Step.apply, h_ab oa ob rfl rfl]
  have hst1_tax : st1.taxVol = st.taxVol := by
    have hw : wrappedCount2 oa ob = 0 := by simp [wrappedCount2, isWrapped, oa, ob, orig]
    simp only [st1, runSteps, Step.apply, hw, Nat.cast_zero, zero_mul, add_zero]
  -- Stage 2: X_{a,i} X_{b,0} via pivot X_{a,0}
  set t2 : List (Asset m × Asset m) := (familyWrappers m a).map (fun x => (x, ob))
  have ht2_map : (familyWrappers m a).map (fun x => Step.triangle x ob oa) =
      t2.map (fun t => Step.triangle t.1 t.2 oa) := by simp [t2, Function.comp_def]
  have ht2_spec := runTriangles_batch D (u a - u b) oa st1 t2
    ((familyWrappers_nodup m a).map (fun x y h => by simpa using h))
    (by intro t ht; simp only [t2, List.mem_map] at ht; rcases ht with ⟨x, hx, rfl⟩
        rw [(mem_familyWrappers m a x).mp hx |>.1]; exact hab)
    (by intro t ht; simp only [t2, List.mem_map] at ht; rcases ht with ⟨x, hx, rfl⟩
        have hxw := (mem_familyWrappers m a x).mp hx
        have hx_ne : x ≠ oa := fun h => hxw.2 (by rw [h]; rfl)
        rw [hst1_res, clearEdge]
        split_ifs with h
        · exfalso
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hx_ne h1
          · exact hab (hxw.1.symm.trans (congrArg Sigma.fst h1))
        · exact h_ab x ob hxw.1 rfl)
    (by intro t ht; simp only [t2, List.mem_map] at ht; rcases ht with ⟨x, hx, rfl⟩
        have hxw := (mem_familyWrappers m a x).mp hx
        refine ⟨fun h => hxw.2 (by dsimp at h; rw [h]; rfl), hoa_ne_ob.symm, ?_, ?_⟩
        · rw [hst1_res, clearEdge]
          split_ifs with h
          · exfalso
            rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact hab (hxw.1.symm.trans (congrArg Sigma.fst h2))
            · exact hab (congrArg Sigma.fst h1)
          · exact h_same_a x hxw.1
        · rw [hst1_res, clearEdge]; simp)
    (by intro t₁ h1 t₂ h2 ⟨heq, _⟩
        simp only [t2, List.mem_map] at h1 h2
        rcases h1 with ⟨x₁, hx1, rfl⟩; rcases h2 with ⟨x₂, _, rfl⟩
        exact hab (((mem_familyWrappers m a x₁).mp hx1).1.symm.trans (congrArg Sigma.fst heq)))
    (by intro t₁ h1 t₂ h2
        simp only [t2, List.mem_map] at h1 h2
        rcases h1 with ⟨x₁, hx1, rfl⟩; rcases h2 with ⟨x₂, hx2, rfl⟩
        have h2w := (mem_familyWrappers m a x₂).mp hx2
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · dsimp at h; exact h2w.2 (by rw [← h]; rfl)
          · exact hab (congrArg Sigma.fst h)
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · dsimp at h; exact h2w.2 (by rw [← h]; rfl)
          · exact hab (congrArg Sigma.fst h))
  rcases ht2_spec with ⟨h2_valid, h2_res, h2_vol, h2_tax⟩
  set st2 := runSteps D st1 (t2.map (fun t => Step.triangle t.1 t.2 oa))
  -- Stage 3: X_{a,0} X_{b,j} via pivot X_{b,0}
  set t3 : List (Asset m × Asset m) := (familyWrappers m b).map (fun y => (oa, y))
  have ht3_map : (familyWrappers m b).map (fun y => Step.triangle oa y ob) =
      t3.map (fun t => Step.triangle t.1 t.2 ob) := by simp [t3, Function.comp_def]
  have ht3_spec := runTriangles_batch D (u a - u b) ob st2 t3
    ((familyWrappers_nodup m b).map (fun x y h => by simpa using h))
    (by intro t ht; simp only [t3, List.mem_map] at ht; rcases ht with ⟨y, hy, rfl⟩
        rw [(mem_familyWrappers m b y).mp hy |>.1]; exact hab)
    (by intro t ht; simp only [t3, List.mem_map] at ht; rcases ht with ⟨y, hy, rfl⟩
        have hyw := (mem_familyWrappers m b y).mp hy
        have hy_ne : y ≠ ob := fun h => hyw.2 (by rw [h]; rfl)
        rw [h2_res]
        split_ifs with h
        · exfalso
          rcases h with ⟨s, hs, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
          · exact hy_ne (by simp only [t2, List.mem_map] at hs; rcases hs with ⟨x, _, rfl⟩; exact h2)
          · simp only [t2, List.mem_map] at hs; rcases hs with ⟨x, _, rfl⟩
            exact hab (congrArg Sigma.fst h1)
        · rw [hst1_res, clearEdge]
          split_ifs with h'
          · exfalso
            rcases h' with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact hy_ne h2
            · exact hab (congrArg Sigma.fst h1)
          · exact h_ab oa y rfl hyw.1)
    (by intro t ht; simp only [t3, List.mem_map] at ht; rcases ht with ⟨y, hy, rfl⟩
        have hyw := (mem_familyWrappers m b y).mp hy
        refine ⟨hoa_ne_ob, fun h => hyw.2 (by dsimp at h; rw [h]; rfl), ?_, ?_⟩
        · rw [h2_res]
          split_ifs with h
          · exfalso
            rcases h with ⟨s, hs, (⟨h1, _⟩ | ⟨_, h2⟩)⟩
            · simp only [t2, List.mem_map] at hs; rcases hs with ⟨x, hx, rfl⟩
              exact hab.symm ((congrArg Sigma.fst h1).trans ((mem_familyWrappers m a x).mp hx).1)
            · simp only [t2, List.mem_map] at hs; rcases hs with ⟨x, hx, rfl⟩
              dsimp at h2
              exact ((mem_familyWrappers m a x).mp hx).2 (by rw [← h2]; rfl)
          · rw [hst1_res, clearEdge]; simp
        · rw [h2_res]
          split_ifs with h
          · exfalso
            rcases h with ⟨s, hs, (⟨h1, _⟩ | ⟨_, h2⟩)⟩
            · simp only [t2, List.mem_map] at hs; rcases hs with ⟨x, hx, rfl⟩
              exact hab.symm ((congrArg Sigma.fst h1).trans ((mem_familyWrappers m a x).mp hx).1)
            · simp only [t2, List.mem_map] at hs; rcases hs with ⟨x, hx, rfl⟩
              exact hab.symm (hyw.1.symm.trans ((congrArg Sigma.fst h2).trans ((mem_familyWrappers m a x).mp hx).1))
          · rw [hst1_res, clearEdge]
            split_ifs with h'
            · exfalso
              rcases h' with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact hab.symm (congrArg Sigma.fst h1)
              · exact hab.symm (hyw.1.symm.trans (congrArg Sigma.fst h2))
            · exact h_same_b y hyw.1)
    (by intro t₁ h1 t₂ h2 ⟨heq, _⟩
        simp only [t3, List.mem_map] at h1 h2
        rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨y₂, hy2, rfl⟩
        exact hab ((congrArg Sigma.fst heq).trans ((mem_familyWrappers m b y₂).mp hy2).1))
    (by intro t₁ h1 t₂ h2
        simp only [t3, List.mem_map] at h1 h2
        rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨y₂, hy2, rfl⟩
        have h2w := (mem_familyWrappers m b y₂).mp hy2
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact hab.symm (congrArg Sigma.fst h)
          · dsimp at h; exact h2w.2 (by rw [← h]; rfl)
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact hab.symm (congrArg Sigma.fst h)
          · dsimp at h; exact h2w.2 (by rw [← h]; rfl))
  rcases ht3_spec with ⟨h3_valid, h3_res, h3_vol, h3_tax⟩
  set st3 := runSteps D st2 (t3.map (fun t => Step.triangle t.1 t.2 ob))
  -- Stage 4: X_{a,i} X_{b,j} via pivot X_{a,0}
  set t4 : List (Asset m × Asset m) :=
    (familyWrappers m a).flatMap (fun x => (familyWrappers m b).map (fun y => (x, y)))
  have ht4_mem : ∀ t : Asset m × Asset m,
      t ∈ t4 ↔ (t.1.1 = a ∧ t.1.2.val ≠ 0) ∧ (t.2.1 = b ∧ t.2.2.val ≠ 0) := by
    intro t
    simp only [t4, List.mem_flatMap, List.mem_map, mem_familyWrappers]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨hx, hy⟩
    · rintro ⟨h1, h2⟩; exact ⟨t.1, h1, t.2, h2, rfl⟩
  have ht4_nodup : t4.Nodup := by
    unfold t4
    rw [List.nodup_flatMap]
    refine ⟨fun x _ => (familyWrappers_nodup m b).map (fun y₁ y₂ h => by simpa using h), ?_⟩
    exact (familyWrappers_nodup m a).imp fun {x₁ x₂} hne p hp1 hp2 => by
      simp only [List.mem_map] at hp1 hp2
      rcases hp1 with ⟨_, _, rfl⟩
      rcases hp2 with ⟨_, _, heq⟩
      exact hne (Prod.mk.inj heq).1.symm
  have ht4_spec := runTriangles_batch D (u a - u b) oa st3 t4
    ht4_nodup
    (by intro t ht; rw [ht4_mem] at ht; rw [ht.1.1, ht.2.1]; exact hab)
    (by intro t ht; rw [ht4_mem] at ht
        rw [h3_res]
        split_ifs with h3'
        · exfalso
          rcases h3' with ⟨s, hs, (⟨h1, _⟩ | ⟨h1, _⟩)⟩
          · simp only [t3, List.mem_map] at hs; rcases hs with ⟨_, _, rfl⟩
            exact ht.1.2 (by rw [h1]; rfl)
          · simp only [t3, List.mem_map] at hs; rcases hs with ⟨y, hy, rfl⟩
            exact hab (ht.1.1.symm.trans ((congrArg Sigma.fst h1).trans ((mem_familyWrappers m b y).mp hy).1))
        · rw [h2_res]
          split_ifs with h2'
          · exfalso
            rcases h2' with ⟨s, hs, (⟨_, h2⟩ | ⟨h1, _⟩)⟩
            · simp only [t2, List.mem_map] at hs; rcases hs with ⟨_, _, rfl⟩
              exact ht.2.2 (by rw [h2]; rfl)
            · simp only [t2, List.mem_map] at hs; rcases hs with ⟨_, _, rfl⟩
              exact hab (ht.1.1.symm.trans (congrArg Sigma.fst h1))
          · rw [hst1_res, clearEdge]
            split_ifs with h1'
            · exfalso
              rcases h1' with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact ht.1.2 (by rw [h1]; rfl)
              · exact hab (ht.1.1.symm.trans (congrArg Sigma.fst h1))
            · exact h_ab t.1 t.2 ht.1.1 ht.2.1)
    (by intro t ht; rw [ht4_mem] at ht
        refine ⟨fun h => ht.1.2 (by rw [h]; rfl),
          fun h => hab (ht.2.1.symm.trans (congrArg Sigma.fst h)).symm, ?_, ?_⟩
        · rw [h3_res]
          split_ifs with h3'
          · exfalso
            rcases h3' with ⟨s, hs, (⟨_, h2⟩ | ⟨h1, _⟩)⟩
            · simp only [t3, List.mem_map] at hs; rcases hs with ⟨y, hy, rfl⟩
              exact hab (ht.1.1.symm.trans ((congrArg Sigma.fst h2).trans ((mem_familyWrappers m b y).mp hy).1))
            · simp only [t3, List.mem_map] at hs; rcases hs with ⟨y, hy, rfl⟩
              exact hab ((congrArg Sigma.fst h1).trans ((mem_familyWrappers m b y).mp hy).1)
          · rw [h2_res]
            split_ifs with h2'
            · exfalso
              rcases h2' with ⟨s, hs, (⟨_, h2⟩ | ⟨h1, _⟩)⟩
              · simp only [t2, List.mem_map] at hs; rcases hs with ⟨_, _, rfl⟩
                exact hab (ht.1.1.symm.trans (congrArg Sigma.fst h2))
              · simp only [t2, List.mem_map] at hs; rcases hs with ⟨_, _, rfl⟩
                exact hab (congrArg Sigma.fst h1)
            · rw [hst1_res, clearEdge]
              split_ifs with h1'
              · exfalso
                rcases h1' with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact hab (ht.1.1.symm.trans (congrArg Sigma.fst h2))
                · exact hab (congrArg Sigma.fst h1)
              · exact h_same_a t.1 ht.1.1
        · rw [h3_res]
          have hmem3 : ∃ s ∈ t3, (oa = s.1 ∧ t.2 = s.2) ∨ (oa = s.2 ∧ t.2 = s.1) :=
            ⟨(oa, t.2), by
              simp only [t3, List.mem_map]
              exact ⟨t.2, (mem_familyWrappers m b t.2).mpr ht.2, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
          simp [hmem3])
    (by intro t₁ h1 t₂ h2 ⟨heq, _⟩
        rw [ht4_mem] at h1 h2
        exact hab (h1.1.1.symm.trans ((congrArg Sigma.fst heq).trans h2.2.1)))
    (by intro t₁ h1 t₂ h2
        rw [ht4_mem] at h1 h2
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact h2.1.2 (by rw [← h]; rfl)
          · exact hab ((congrArg Sigma.fst h).trans h2.2.1)
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact h2.1.2 (by rw [← h]; rfl)
          · exact hab ((congrArg Sigma.fst h).trans h2.2.1))
  rcases ht4_spec with ⟨h4_valid, h4_res, h4_vol, h4_tax⟩
  -- Combine all 4 stages
  have hsched : pairSchedule m hm a b =
      [Step.external oa ob] ++
      t2.map (fun t => Step.triangle t.1 t.2 oa) ++
      t3.map (fun t => Step.triangle t.1 t.2 ob) ++
      t4.map (fun t => Step.triangle t.1 t.2 oa) := by
    simp [pairSchedule, ht2_map, ht3_map, oa, ob, t4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsched, validTrace_append, validTrace_append, validTrace_append]
    refine ⟨⟨⟨h1_valid, h2_valid⟩, ?_⟩, ?_⟩
    · rw [runSteps_append]; exact h3_valid
    · rw [runSteps_append, runSteps_append]; exact h4_valid
  · intro p q
    rw [hsched, runSteps_append, runSteps_append, runSteps_append]
    change (runSteps D st3 (t4.map (fun t => Step.triangle t.1 t.2 oa))).res p q = _
    rw [h4_res, h3_res, h2_res, hst1_res, clearEdge]
    by_cases hpq : (p.1 = a ∧ q.1 = b) ∨ (p.1 = b ∧ q.1 = a)
    · simp only [hpq, ↓reduceIte]
      have hcov :
          (∃ t ∈ t4, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1)) ∨
          (∃ t ∈ t3, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1)) ∨
          (∃ t ∈ t2, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1)) ∨
          ((p = oa ∧ q = ob) ∨ (p = ob ∧ q = oa)) := by
        have horig : ∀ x : Asset m, ∀ c : Fin M, x.1 = c → x.2.val = 0 → x = orig m hm c := by
          rintro ⟨c', ⟨v, hv⟩⟩ c h1 h2
          dsimp at h1 h2
          subst h1; subst h2; rfl
        rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
        · by_cases hp0 : p.2.val = 0 <;> by_cases hq0 : q.2.val = 0
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨horig p a hp hp0, horig q b hq hq0⟩)))
          · exact Or.inr (Or.inl ⟨(oa, q), by
              simp only [t3, List.mem_map]
              exact ⟨q, (mem_familyWrappers m b q).mpr ⟨hq, hq0⟩, rfl⟩,
              Or.inl ⟨horig p a hp hp0, rfl⟩⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨(p, ob), by
              simp only [t2, List.mem_map]
              exact ⟨p, (mem_familyWrappers m a p).mpr ⟨hp, hp0⟩, rfl⟩,
              Or.inl ⟨rfl, horig q b hq hq0⟩⟩))
          · exact Or.inl ⟨(p, q), (ht4_mem (p, q)).mpr ⟨⟨hp, hp0⟩, ⟨hq, hq0⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
        · by_cases hp0 : p.2.val = 0 <;> by_cases hq0 : q.2.val = 0
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨horig p b hp hp0, horig q a hq hq0⟩)))
          · exact Or.inr (Or.inr (Or.inl ⟨(q, ob), by
              simp only [t2, List.mem_map]
              exact ⟨q, (mem_familyWrappers m a q).mpr ⟨hq, hq0⟩, rfl⟩,
              Or.inr ⟨horig p b hp hp0, rfl⟩⟩))
          · exact Or.inr (Or.inl ⟨(oa, p), by
              simp only [t3, List.mem_map]
              exact ⟨p, (mem_familyWrappers m b p).mpr ⟨hp, hp0⟩, rfl⟩,
              Or.inr ⟨rfl, horig q a hq hq0⟩⟩)
          · exact Or.inl ⟨(q, p), (ht4_mem (q, p)).mpr ⟨⟨hq, hq0⟩, ⟨hp, hp0⟩⟩, Or.inr ⟨rfl, rfl⟩⟩
      rcases hcov with h4 | h3 | h2 | h1
      · simp [h4]
      · by_cases h4 : ∃ t ∈ t4, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) <;> simp [h4, h3]
      · by_cases h4 : ∃ t ∈ t4, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) <;>
        by_cases h3 : ∃ t ∈ t3, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) <;> simp [h4, h3, h2]
      · by_cases h4 : ∃ t ∈ t4, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) <;>
        by_cases h3 : ∃ t ∈ t3, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) <;>
        by_cases h2 : ∃ t ∈ t2, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) <;> simp [h4, h3, h2, h1]
    · have hn4 : ¬ ∃ t ∈ t4, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) := by
        rintro ⟨t, ht, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · rw [ht4_mem] at ht; exact hpq (Or.inl ⟨ht.1.1, ht.2.1⟩)
        · rw [ht4_mem] at ht; exact hpq (Or.inr ⟨ht.2.1, ht.1.1⟩)
      have hn3 : ¬ ∃ t ∈ t3, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) := by
        rintro ⟨t, ht, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;>
        · simp only [t3, List.mem_map] at ht; rcases ht with ⟨y, hy, rfl⟩
          have hyw := (mem_familyWrappers m b y).mp hy
          exact hpq (by simp [oa, orig, hyw.1])
      have hn2 : ¬ ∃ t ∈ t2, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1) := by
        rintro ⟨t, ht, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;>
        · simp only [t2, List.mem_map] at ht; rcases ht with ⟨x, hx, rfl⟩
          have hxw := (mem_familyWrappers m a x).mp hx
          exact hpq (by simp [ob, orig, hxw.1])
      have hn1 : ¬ ((p = oa ∧ q = ob) ∨ (p = ob ∧ q = oa)) := by
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hpq (by simp [oa, ob, orig])
      simp [hpq, hn4, hn3, hn2, hn1]
  · -- Volume accumulation
    rw [hsched, runSteps_append, runSteps_append, runSteps_append]
    change (runSteps D st3 (t4.map (fun t => Step.triangle t.1 t.2 oa))).vol = _
    rw [h4_vol, h3_vol, h2_vol, hst1_vol]
    have hl2 : t2.length = m a - 1 := by simp [t2, familyWrappers_length m hm a]
    have hl3 : t3.length = m b - 1 := by simp [t3, familyWrappers_length m hm b]
    have hl4 : t4.length = (m a - 1) * (m b - 1) := by
      simp [t4, List.length_flatMap, familyWrappers_length m hm a, familyWrappers_length m hm b]
    rw [hl2, hl3, hl4, Nat.cast_mul, Nat.cast_sub hma_pos, Nat.cast_sub hmb_pos]
    simp only [Nat.cast_one]
    ring
  · -- Taxable wrapped-transfer volume accumulation
    rw [hsched, runSteps_append, runSteps_append, runSteps_append]
    change (runSteps D st3 (t4.map (fun t => Step.triangle t.1 t.2 oa))).taxVol = _
    rw [h4_tax, h3_tax, h2_tax, hst1_tax]
    have hs2 : (t2.map (fun t =>
        wrappedCount3 t.1 t.2 oa + wrappedCount2 oa t.1 + wrappedCount2 oa t.2)).sum =
        2 * (m a - 1) := by
      have hmap : t2.map (fun t =>
          wrappedCount3 t.1 t.2 oa + wrappedCount2 oa t.1 + wrappedCount2 oa t.2) =
          List.replicate (m a - 1) 2 := by
        apply List.ext_getElem
        · simp [t2, familyWrappers_length m hm a]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_replicate, t2]
          have hmem : (familyWrappers m a)[i]'(by simpa [t2] using h1) ∈ familyWrappers m a :=
            List.getElem_mem _
          have hxw := (mem_familyWrappers m a _).mp hmem
          have hwx : isWrapped ((familyWrappers m a)[i]'(by simpa [t2] using h1)) = true := by
            simp [isWrapped, hxw.2]
          have hwoa : isWrapped oa = false := by simp [isWrapped, oa, orig]
          have hwob : isWrapped ob = false := by simp [isWrapped, ob, orig]
          simp [wrappedCount3, wrappedCount2, hwx, hwoa, hwob]
      rw [hmap, List.sum_replicate, smul_eq_mul, mul_comm]
    have hs3 : (t3.map (fun t =>
        wrappedCount3 t.1 t.2 ob + wrappedCount2 ob t.1 + wrappedCount2 ob t.2)).sum =
        2 * (m b - 1) := by
      have hmap : t3.map (fun t =>
          wrappedCount3 t.1 t.2 ob + wrappedCount2 ob t.1 + wrappedCount2 ob t.2) =
          List.replicate (m b - 1) 2 := by
        apply List.ext_getElem
        · simp [t3, familyWrappers_length m hm b]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_replicate, t3]
          have hmem : (familyWrappers m b)[i]'(by simpa [t3] using h1) ∈ familyWrappers m b :=
            List.getElem_mem _
          have hyw := (mem_familyWrappers m b _).mp hmem
          have hwy : isWrapped ((familyWrappers m b)[i]'(by simpa [t3] using h1)) = true := by
            simp [isWrapped, hyw.2]
          have hwoa : isWrapped oa = false := by simp [isWrapped, oa, orig]
          have hwob : isWrapped ob = false := by simp [isWrapped, ob, orig]
          simp [wrappedCount3, wrappedCount2, hwy, hwoa, hwob]
      rw [hmap, List.sum_replicate, smul_eq_mul, mul_comm]
    have hs4 : (t4.map (fun t =>
        wrappedCount3 t.1 t.2 oa + wrappedCount2 oa t.1 + wrappedCount2 oa t.2)).sum =
        4 * ((m a - 1) * (m b - 1)) := by
      have hlen4 : t4.length = (m a - 1) * (m b - 1) := by
        simp [t4, List.length_flatMap, familyWrappers_length m hm a, familyWrappers_length m hm b]
      have hmap : t4.map (fun t =>
          wrappedCount3 t.1 t.2 oa + wrappedCount2 oa t.1 + wrappedCount2 oa t.2) =
          List.replicate ((m a - 1) * (m b - 1)) 4 := by
        apply List.ext_getElem
        · simp [hlen4]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_replicate]
          have hmem : t4[i]'(by simpa using h1) ∈ t4 := List.getElem_mem _
          have htw := (ht4_mem _).mp hmem
          have hw1 : isWrapped (t4[i]'(by simpa using h1)).1 = true := by simp [isWrapped, htw.1.2]
          have hw2 : isWrapped (t4[i]'(by simpa using h1)).2 = true := by simp [isWrapped, htw.2.2]
          have hwoa : isWrapped oa = false := by simp [isWrapped, oa, orig]
          simp [wrappedCount3, wrappedCount2, hw1, hw2, hwoa]
      rw [hmap, List.sum_replicate, smul_eq_mul, mul_comm]
    rw [hs2, hs3, hs4]
    push_cast [Nat.cast_sub hma_pos, Nat.cast_sub hmb_pos]
    ring

private theorem unorderedPairList_nodup (M : ℕ) : (unorderedPairList M).Nodup := by
  unfold unorderedPairList
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => ((List.nodup_finRange M).filter _).map (fun b₁ b₂ h => by simpa using h), ?_⟩
  exact (List.nodup_finRange M).imp fun {a₁ a₂} hne p hp1 hp2 => by
    simp only [List.mem_map] at hp1 hp2
    rcases hp1 with ⟨_, _, rfl⟩
    rcases hp2 with ⟨_, _, heq⟩
    exact hne (Prod.mk.inj heq).1.symm

private theorem mem_unorderedPairList (M : ℕ) (p : Fin M × Fin M) :
    p ∈ unorderedPairList M ↔ p.1 < p.2 := by
  simp only [unorderedPairList, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, rfl⟩; exact hab
  · intro hab; exact ⟨p.1, p.2, hab, by cases p; rfl⟩

private theorem unorderedPairList_toFinset (M : ℕ) :
    (unorderedPairList M).toFinset = unorderedPairs M := by
  ext p
  simp [List.mem_toFinset, mem_unorderedPairList, unorderedPairs]

/-- Inductive fold over any duplicate-free list of strictly ordered family pairs `a < b`. -/
private theorem runPairs_spec {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    (u : Fin M → ℝ) (D : ℝ) (pairs : List (Fin M × Fin M))
    (hnodup : pairs.Nodup) (hlt : ∀ p ∈ pairs, p.1 < p.2)
    (st : GraphState m)
    (h_same : ∀ x y : Asset m, x.1 = y.1 → st.res x y = 0)
    (h_untouched : ∀ p ∈ pairs, ∀ x y : Asset m, x.1 = p.1 → y.1 = p.2 → st.res x y = u p.1 - u p.2) :
    let sched := pairs.flatMap (fun p => pairSchedule m hm p.1 p.2)
    let st' := runSteps D st sched
    ValidTrace D st sched ∧
    (∀ x y, st'.res x y =
      if ∃ p ∈ pairs, (x.1 = p.1 ∧ y.1 = p.2) ∨ (x.1 = p.2 ∧ y.1 = p.1) then 0 else st.res x y) ∧
    st'.vol = st.vol +
      (pairs.map (fun p => (5 * (m p.1 : ℝ) * (m p.2 : ℝ) - 4) * D * |u p.1 - u p.2|)).sum ∧
    st'.taxVol = st.taxVol +
      (pairs.map (fun p =>
        (4 * (m p.1 : ℝ) * (m p.2 : ℝ) - 2 * (m p.1 : ℝ) - 2 * (m p.2 : ℝ)) *
          D * |u p.1 - u p.2|)).sum := by
  induction pairs generalizing st with
  | nil => simp [ValidTrace, runSteps]
  | cons hd tl ih =>
    rcases List.nodup_cons.mp hnodup with ⟨hd_notin, tl_nodup⟩
    have hhd_lt : hd.1 < hd.2 := hlt hd List.mem_cons_self
    have h1 := pairSchedule_spec m hm u D hd.1 hd.2 hhd_lt.ne st
      (fun x hx => h_same (orig m hm hd.1) x hx.symm)
      (fun y hy => h_same (orig m hm hd.2) y hy.symm)
      (h_untouched hd List.mem_cons_self)
    rcases h1 with ⟨h1_valid, h1_res, h1_vol, h1_tax⟩
    set st1 := runSteps D st (pairSchedule m hm hd.1 hd.2)
    have hst1_same : ∀ x y : Asset m, x.1 = y.1 → st1.res x y = 0 := by
      intro x y hxy
      rw [h1_res]
      split_ifs
      · rfl
      · exact h_same x y hxy
    have hst1_untouched : ∀ p ∈ tl, ∀ x y : Asset m,
        x.1 = p.1 → y.1 = p.2 → st1.res x y = u p.1 - u p.2 := by
      intro p hp x y hx hy
      have hp_lt : p.1 < p.2 := hlt p (List.mem_cons_of_mem hd hp)
      rw [h1_res]
      split_ifs with h
      · exfalso
        rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact hd_notin (by cases p; cases hd; simp_all)
        · have heq1 : hd.1 = p.2 := h2'.symm.trans hy
          have heq2 : hd.2 = p.1 := h1'.symm.trans hx
          have : p.2 < p.1 := by rw [← heq1, ← heq2]; exact hhd_lt
          exact lt_asymm hp_lt this
      · exact h_untouched p (List.mem_cons_of_mem hd hp) x y hx hy
    have h2 := ih tl_nodup (fun p hp => hlt p (List.mem_cons_of_mem hd hp)) st1 hst1_same hst1_untouched
    rcases h2 with ⟨h2_valid, h2_res, h2_vol, h2_tax⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, validTrace_append]
      exact ⟨h1_valid, h2_valid⟩
    · intro x y
      simp only [List.flatMap_cons, runSteps_append]
      change (runSteps D st1 (tl.flatMap (fun p => pairSchedule m hm p.1 p.2))).res x y = _
      rw [h2_res, h1_res]
      simp only [List.mem_cons, exists_eq_or_imp]
      by_cases htl : ∃ p ∈ tl, (x.1 = p.1 ∧ y.1 = p.2) ∨ (x.1 = p.2 ∧ y.1 = p.1)
      · simp [htl]
      · by_cases hhd : (x.1 = hd.1 ∧ y.1 = hd.2) ∨ (x.1 = hd.2 ∧ y.1 = hd.1)
        · simp [htl, hhd]
        · simp [htl, hhd]
    · simp only [List.flatMap_cons, runSteps_append, List.map_cons, List.sum_cons]
      change (runSteps D st1 (tl.flatMap (fun p => pairSchedule m hm p.1 p.2))).vol = _
      rw [h2_vol, h1_vol]
      ring
    · simp only [List.flatMap_cons, runSteps_append, List.map_cons, List.sum_cons]
      change (runSteps D st1 (tl.flatMap (fun p => pairSchedule m hm p.1 p.2))).taxVol = _
      rw [h2_tax, h1_tax]
      ring

private theorem list_sum_unorderedPairList {M : ℕ} (f : Fin M × Fin M → ℝ) :
    ((unorderedPairList M).map f).sum = ∑ p ∈ unorderedPairs M, f p := by
  rw [← unorderedPairList_toFinset M, List.sum_toFinset _ (unorderedPairList_nodup M)]

/-- **Main Execution Soundness Theorem (Sections 1, 2, & 5):**
Running the explicit complete-graph cascade schedule from consistent shock vector `u`:
1. Satisfies every support-fairness precondition at every step (`ValidTrace`).
2. Leaves every pool in the complete graph arbitrage-free (`res x y = 0`).
3. Produces exact aggregate pool turnover `V = D ∑_{a<b} (5 m_a m_b - 4) |u_a - u_b|`.
4. Produces exact taxable wrapped-transfer turnover
   `T = D ∑_{a<b} (4 m_a m_b - 2 m_a - 2 m_b) |u_a - u_b|`. -/
theorem cascadeSchedule_spec {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    (u : Fin M → ℝ) (D : ℝ) :
    let final := runSteps D (initState m u) (cascadeSchedule m hm)
    ValidTrace D (initState m u) (cascadeSchedule m hm) ∧
    (∀ x y : Asset m, final.res x y = 0) ∧
    final.vol = D * ∑ p ∈ unorderedPairs M,
      (5 * (m p.1 : ℝ) * (m p.2 : ℝ) - 4) * |u p.1 - u p.2| ∧
    final.taxVol = D * ∑ p ∈ unorderedPairs M,
      (4 * (m p.1 : ℝ) * (m p.2 : ℝ) - 2 * (m p.1 : ℝ) - 2 * (m p.2 : ℝ)) * |u p.1 - u p.2| := by
  have h := runPairs_spec m hm u D (unorderedPairList M)
    (unorderedPairList_nodup M) (fun p hp => (mem_unorderedPairList M p).mp hp)
    (initState m u)
    (fun x y hxy => by simp [initState, hxy])
    (fun p _ x y hx hy => by simp [initState, hx, hy])
  rcases h with ⟨hval, hres, hvol, htax⟩
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro x y
    unfold cascadeSchedule
    rw [hres]
    by_cases hxy : x.1 = y.1
    · split_ifs
      · rfl
      · simp [initState, hxy]
    · have hor : x.1 < y.1 ∨ y.1 < x.1 := lt_or_gt_of_ne hxy
      have hex : ∃ p ∈ unorderedPairList M, (x.1 = p.1 ∧ y.1 = p.2) ∨ (x.1 = p.2 ∧ y.1 = p.1) := by
        rcases hor with hlt | hgt
        · exact ⟨(x.1, y.1), (mem_unorderedPairList M (x.1, y.1)).mpr hlt, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨(y.1, x.1), (mem_unorderedPairList M (y.1, x.1)).mpr hgt, Or.inr ⟨rfl, rfl⟩⟩
      simp [hex]
  · unfold cascadeSchedule
    rw [hvol, list_sum_unorderedPairList, Finset.mul_sum]
    simp only [initState, zero_add]
    refine Finset.sum_congr rfl fun p _ => by ring
  · unfold cascadeSchedule
    rw [htax, list_sum_unorderedPairList, Finset.mul_sum]
    simp only [initState, zero_add]
    refine Finset.sum_congr rfl fun p _ => by ring

/-- Exact taxable wrapped-transfer turnover for the direct-correction baseline schedule. -/
theorem directSchedule_taxVol {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    (u : Fin M → ℝ) (D : ℝ) :
    (runSteps D (initState m u) (directSchedule m)).taxVol =
      D * ∑ p ∈ unorderedPairs M,
        (2 * (m p.1 : ℝ) * (m p.2 : ℝ) - (m p.1 : ℝ) - (m p.2 : ℝ)) * |u p.1 - u p.2| := by
  have hpair : ∀ (a b : Fin M) (hab : a ≠ b) (st : GraphState m),
      (∀ x y : Asset m, x.1 = a → y.1 = b → st.res x y = u a - u b) →
      (∀ p q, (runSteps D st (pairDirectSchedule m a b)).res p q =
        if (p.1 = a ∧ q.1 = b) ∨ (p.1 = b ∧ q.1 = a) then 0 else st.res p q) ∧
      (runSteps D st (pairDirectSchedule m a b)).taxVol = st.taxVol +
        (2 * (m a : ℝ) * (m b : ℝ) - (m a : ℝ) - (m b : ℝ)) * D * |u a - u b| := by
    intro a b hab st h_ab
    set tlist : List (Asset m × Asset m) :=
      (familyAllAssets m a).flatMap (fun x => (familyAllAssets m b).map (fun y => (x, y)))
    have ht_mem : ∀ t : Asset m × Asset m, t ∈ tlist ↔ t.1.1 = a ∧ t.2.1 = b := by
      intro t
      simp only [tlist, familyAllAssets, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        rcases t with ⟨⟨a', i⟩, ⟨b', j⟩⟩
        dsimp at h1 h2; subst h1; subst h2
        exact ⟨⟨a', i⟩, ⟨i, rfl⟩, ⟨b', j⟩, ⟨j, rfl⟩, rfl⟩
    have ht_nodup : tlist.Nodup := by
      unfold tlist familyAllAssets
      rw [List.nodup_flatMap]
      refine ⟨fun x _ => ((List.nodup_finRange (m b)).map (fun i j h => by simpa using h)).map
        (fun y₁ y₂ h => by simpa using h), ?_⟩
      exact ((List.nodup_finRange (m a)).map (fun i j h => by simpa using h)).imp
        fun {x₁ x₂} hne p hp1 hp2 => by
          simp only [List.mem_map] at hp1 hp2
          rcases hp1 with ⟨_, _, rfl⟩; rcases hp2 with ⟨_, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
    have hbatch := runExternals_batch D (u a - u b) st tlist ht_nodup
      (by intro t ht; rw [ht_mem] at ht; rw [ht.1, ht.2]; exact hab)
      (by intro t ht; rw [ht_mem] at ht; exact h_ab t.1 t.2 ht.1 ht.2)
      (by intro t₁ h1 t₂ h2 ⟨heq, _⟩; rw [ht_mem] at h1 h2
          exact hab (h1.1.symm.trans ((congrArg Sigma.fst heq).trans h2.2)))
    rcases hbatch with ⟨_, hres_b, _, htax_b⟩
    refine ⟨?_, ?_⟩
    · intro p q
      change (runSteps D st (tlist.map (fun t => Step.external t.1 t.2))).res p q = _
      rw [hres_b]
      have hiff : (∃ t ∈ tlist, (p = t.1 ∧ q = t.2) ∨ (p = t.2 ∧ q = t.1)) ↔
          (p.1 = a ∧ q.1 = b) ∨ (p.1 = b ∧ q.1 = a) := by
        constructor
        · rintro ⟨t, ht, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
          · rw [ht_mem] at ht; exact Or.inl ht
          · rw [ht_mem] at ht; exact Or.inr ⟨ht.2, ht.1⟩
        · rintro (⟨hp, hq⟩ | ⟨hp, hq⟩)
          · exact ⟨(p, q), (ht_mem (p, q)).mpr ⟨hp, hq⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨(q, p), (ht_mem (q, p)).mpr ⟨hq, hp⟩, Or.inr ⟨rfl, rfl⟩⟩
      simp [hiff]
    · change (runSteps D st (tlist.map (fun t => Step.external t.1 t.2))).taxVol = _
      rw [htax_b]
      have hsum_fin : ∀ k : ℕ,
          ((List.finRange (k + 1)).map (fun i : Fin (k + 1) =>
            if (i.val != 0) = true then (1 : ℕ) else 0)).sum = k := by
        intro k
        rw [List.finRange_succ, List.map_cons, List.map_map]
        simp only [Fin.val_zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.sum_cons,
          zero_add, Function.comp_def]
        have hones : (List.finRange k).map
            (fun x : Fin k => if (x.succ.val != 0) = true then (1 : ℕ) else 0) =
            List.replicate k 1 := by
          apply List.ext_getElem
          · simp
          · intro i h1 h2; simp [Fin.val_succ]
        rw [hones, List.sum_replicate, smul_eq_mul, mul_one]
      have hsum_w : ∀ c : Fin M,
          ((familyAllAssets m c).map (fun x => if isWrapped x then (1 : ℕ) else 0)).sum = m c - 1 := by
        intro c
        have h1 : (familyAllAssets m c).map (fun x => if isWrapped x then (1 : ℕ) else 0) =
            (List.finRange (m c)).map (fun i : Fin (m c) =>
              if (i.val != 0) = true then (1 : ℕ) else 0) := by
          simp [familyAllAssets, isWrapped]
        rw [h1]
        have hpos := hm c
        generalize m c = n at hpos ⊢
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [hsum_fin k]
        omega
      have hlen_all : ∀ c : Fin M, (familyAllAssets m c).length = m c := by
        intro c; simp [familyAllAssets]
      have hinner : ∀ x : Asset m,
          (((familyAllAssets m b).map (fun y => (x, y))).map (fun t => wrappedCount2 t.1 t.2)).sum =
          (if isWrapped x then 1 else 0) * m b + (m b - 1) := by
        intro x
        rw [← hsum_w b, ← hlen_all b]
        induction familyAllAssets m b with
        | nil => simp
        | cons y ys ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, wrappedCount2] at ih ⊢
          rw [ih]
          cases isWrapped x <;> cases isWrapped y <;> simp <;> omega
      have hsum_flat : ∀ l : List (Asset m),
          ((l.flatMap (fun x => (familyAllAssets m b).map (fun y => (x, y)))).map
            (fun t => wrappedCount2 t.1 t.2)).sum =
          (l.map (fun x => if isWrapped x then (1 : ℕ) else 0)).sum * m b +
            l.length * (m b - 1) := by
        intro l
        induction l with
        | nil => simp
        | cons x xs ih =>
          simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
            List.sum_cons, List.length_cons]
          rw [hinner x, ih]
          ring
      have hsum_pair : (tlist.map (fun t => wrappedCount2 t.1 t.2)).sum =
          (m a - 1) * m b + m a * (m b - 1) := by
        rw [hsum_flat, hsum_w a, hlen_all a]
      rw [hsum_pair]
      have hma : 1 ≤ m a := hm a
      have hmb : 1 ≤ m b := hm b
      push_cast [Nat.cast_sub hma, Nat.cast_sub hmb]
      ring
  -- Fold over unorderedPairList M
  have hfold : ∀ (pairs : List (Fin M × Fin M)), pairs.Nodup → (∀ p ∈ pairs, p.1 < p.2) →
      ∀ (st : GraphState m),
      (∀ p ∈ pairs, ∀ x y : Asset m, x.1 = p.1 → y.1 = p.2 → st.res x y = u p.1 - u p.2) →
      (runSteps D st (pairs.flatMap (fun p => pairDirectSchedule m p.1 p.2))).taxVol = st.taxVol +
        (pairs.map (fun p =>
          (2 * (m p.1 : ℝ) * (m p.2 : ℝ) - (m p.1 : ℝ) - (m p.2 : ℝ)) * D * |u p.1 - u p.2|)).sum := by
    intro pairs hnd hlt
    induction pairs with
    | nil => intro st _; simp [runSteps]
    | cons hd tl ih =>
      intro st hunt
      rcases List.nodup_cons.mp hnd with ⟨hd_notin, tl_nd⟩
      have hhd_lt := hlt hd List.mem_cons_self
      have h1 := hpair hd.1 hd.2 hhd_lt.ne st (hunt hd List.mem_cons_self)
      set st1 := runSteps D st (pairDirectSchedule m hd.1 hd.2)
      have h2 := ih tl_nd (fun p hp => hlt p (List.mem_cons_of_mem hd hp)) st1 (by
        intro p hp x y hx hy
        have hp_lt := hlt p (List.mem_cons_of_mem hd hp)
        rw [h1.1]
        split_ifs with h
        · exfalso
          rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · exact hd_notin (by cases p; cases hd; simp_all)
          · have heq1 : hd.1 = p.2 := h2'.symm.trans hy
            have heq2 : hd.2 = p.1 := h1'.symm.trans hx
            have : p.2 < p.1 := by rw [← heq1, ← heq2]; exact hhd_lt
            exact lt_asymm hp_lt this
        · exact hunt p (List.mem_cons_of_mem hd hp) x y hx hy)
      simp only [List.flatMap_cons, runSteps_append, List.map_cons, List.sum_cons]
      change (runSteps D st1 (tl.flatMap (fun p => pairDirectSchedule m p.1 p.2))).taxVol = _
      rw [h2, h1.2]
      ring
  have hres := hfold (unorderedPairList M) (unorderedPairList_nodup M)
    (fun p hp => (mem_unorderedPairList M p).mp hp) (initState m u)
    (fun p _ x y hx hy => by simp [initState, hx, hy])
  change (runSteps D (initState m u) (directSchedule m)).taxVol = _
  rw [directSchedule, hres, list_sum_unorderedPairList, Finset.mul_sum]
  simp only [initState, zero_add]
  refine Finset.sum_congr rfl fun p _ => by ring

/-- **Section 2 Doubling Result (holds even for unequal family sizes):**
The complete-graph cascade generates exactly **2×** the taxable wrapped-transfer volume of
direct correction across all pools. -/
theorem cascadeSchedule_doubles_direct {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    (u : Fin M → ℝ) (D : ℝ) :
    (runSteps D (initState m u) (cascadeSchedule m hm)).taxVol =
      2 * (runSteps D (initState m u) (directSchedule m)).taxVol := by
  rw [(cascadeSchedule_spec m hm u D).2.2.2, directSchedule_taxVol m hm u D]
  rw [← mul_assoc, mul_comm 2 D, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => by ring

/-- **Result Boxed Formulas (Equal Family Sizes `m = n + 1`, `D = κ L`):**
* `V = (5 m^2 - 4) κ L S_M`
* `T = 4 n (n + 1) κ L S_M`
* Leading-order burn `B₁ = f T = 4 f κ L n (n + 1) S_M`. -/
theorem equalFamily_boxed_formulas {M n : ℕ} (u : Fin M → ℝ) (κ L f : ℝ) :
    let m : Fin M → ℕ := fun _ => n + 1
    let hm : ∀ a, 0 < m a := fun _ => Nat.succ_pos n
    let final := runSteps (κ * L) (initState m u) (cascadeSchedule m hm)
    final.vol = (5 * ((n : ℝ) + 1) ^ 2 - 4) * κ * L * totalShock u ∧
    final.taxVol = 4 * (n : ℝ) * ((n : ℝ) + 1) * κ * L * totalShock u ∧
    f * final.taxVol = 4 * f * κ * L * (n : ℝ) * ((n : ℝ) + 1) * totalShock u := by
  intro m hm final
  have hspec := cascadeSchedule_spec m hm u (κ * L)
  have hV : final.vol = (5 * ((n : ℝ) + 1) ^ 2 - 4) * κ * L * totalShock u := by
    rw [hspec.2.2.1, totalShock]
    simp only [m, Nat.cast_add, Nat.cast_one]
    rw [← Finset.mul_sum]
    ring
  have hT : final.taxVol = 4 * (n : ℝ) * ((n : ℝ) + 1) * κ * L * totalShock u := by
    rw [hspec.2.2.2, totalShock]
    simp only [m, Nat.cast_add, Nat.cast_one]
    have hcoeff : ∀ p : Fin M × Fin M,
        (4 * ((n : ℝ) + 1) * ((n : ℝ) + 1) - 2 * ((n : ℝ) + 1) - 2 * ((n : ℝ) + 1)) *
          |u p.1 - u p.2| =
        (4 * (n : ℝ) * ((n : ℝ) + 1)) * |u p.1 - u p.2| := fun p => by ring
    simp_rw [hcoeff]
    rw [← Finset.mul_sum]
    ring
  refine ⟨hV, hT, ?_⟩
  rw [hT]
  ring

end CompleteGraphSchedule

end Cascades
