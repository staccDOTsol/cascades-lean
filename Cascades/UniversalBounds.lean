import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Cascades.SingleTarget
import Cascades.GraphSchedule
import Cascades.YieldScaling

/-!
# Routing-Independent Universal Bounds & Surplus Conservation

Answers the natural game-theoretic objection to any single feasible execution schedule:
*"What if rational MEV searchers choose a different route, ordering, direct swap, partial
triangles, or stop early under gas/fee friction `δ`?"*

Formalizes and proves (within the same local equal-depth `D = κ L` model):
1. **Arbitrage Surplus Conservation (`cascade_total_profit_hasSum`, `cascade_total_profit_eq_direct`):**
   Summing triangular profit plus both external support-restoration profits over all cascade
   rounds `k ≥ 0` yields `D * r₀^2 / 2`, identically equal to single-hop direct arbitrage profit.
2. **Arbitrary Execution Traces (`SwapLeg`, `applySwaps`):**
   Models **any** finite sequence `σ` of swaps across any pools in the complete graph, in any
   order, with any signed trade sizes, executed by any mix of competing arbitrageurs.
3. **Universal Volume & Wrapped-Interface Lower Bounds (`any_equilibrium_vol_ge`,
   `any_equilibrium_interface_ge`):**
   Whenever `σ` reaches a `δ`-no-arbitrage equilibrium (`|res_final x y| ≤ δ` on all cross-family
   pools, modeling any gas/burn stopping threshold `δ ≥ 0`):
   * `traceVol σ ≥ D * ∑_{a<b} m_a m_b * max (|u_a - u_b| - δ) 0`
   * `wrappedInterfaceFlow σ ≥ D * ∑_{a<b} (2 m_a m_b - m_a - m_b) * max (|u_a - u_b| - δ) 0`
4. **Universal Wrapped-Transfer Lower Bounds (`any_equilibrium_taxVol_ge_shared`,
   `any_equilibrium_taxVol_ge_unshared`):**
   Models token transfers explicitly with at most 1 sender pool and 1 receiver pool per transfer
   (so each transfer settles at most 2 pool interfaces). Proves that **every** clearing execution,
   even under an adversarial burn-minimizing router with maximum cross-pool transfer sharing,
   must generate at least:
   * `T(txs) ≥ (D / 2) * ∑_{a<b} (2 m_a m_b - m_a - m_b) * max (|u_a - u_b| - δ) 0`
   * For equal families (`m_a = n + 1`, `δ = 0`): `T(txs) ≥ n(n+1) κ L S_M = (1/4) T_cascade`
     (and `≥ 2 n(n+1) κ L S_M = (1/2) T_cascade` without cross-pool transfer sharing).
5. **Routing-Independent Increasing Yield Floor (`yieldFloor_step_pos`, `yieldFloor_tendsto`):**
   Even the worst-case burn-minimizing rational clearing equilibrium has a strictly increasing
   leading gross burn yield floor `Y_floor(M) = f κ n μ (M - 1) / (M(n + 1) - 1)` converging
   to `f κ n μ / (n + 1) > 0` as `M → ∞`.
-/

namespace Cascades

section SurplusConservation

/-- Direct external arbitrage profit on a single pool of depth `D` and residual `r` with trade
size `q`: `Π_direct(q) = r * q - q^2 / (2 * D)`. -/
noncomputable def directProfit (D r q : ℝ) : ℝ :=
  r * q - q ^ 2 / (2 * D)

/-- Direct arbitrage is maximized at `q = D * r` with value `D * r^2 / 2`. -/
theorem directProfit_opt_val {D : ℝ} (hD : D ≠ 0) (r : ℝ) :
    directProfit D r (D * r) = D * r ^ 2 / 2 := by
  unfold directProfit
  field_simp [hD]
  ring

theorem directProfit_le_opt {D : ℝ} (hD : 0 < D) (r q : ℝ) :
    directProfit D r q ≤ directProfit D r (D * r) := by
  rw [directProfit_opt_val hD.ne']
  unfold directProfit
  have hsq : directProfit D r q = D * r ^ 2 / 2 - (q - D * r) ^ 2 / (2 * D) := by
    unfold directProfit; field_simp [hD.ne']; ring
  unfold directProfit at hsq
  have hnn : 0 ≤ (q - D * r) ^ 2 / (2 * D) := by positivity
  linarith

/-- Total profit extracted in cascade round `k`: one optimal triangle trade `q_k = D r_k / 3`
plus two external support-pool restorations (each restoring residual `r_k / 3`). -/
noncomputable def cascadeRoundProfit (D ε : ℝ) (k : ℕ) : ℝ :=
  triangleProfit D (residualSeq ε k) (tradeSeq D ε k) +
    2 * directProfit D (residualSeq ε k / 3) (D * (residualSeq ε k / 3))

theorem cascadeRoundProfit_closed {D : ℝ} (hD : D ≠ 0) (ε : ℝ) (k : ℕ) :
    cascadeRoundProfit D ε k = (5 / 18 : ℝ) * D * ε ^ 2 * (4 / 9 : ℝ) ^ k := by
  unfold cascadeRoundProfit tradeSeq
  rw [triangleProfit_opt_val hD, directProfit_opt_val hD, residualSeq_closed]
  have hpow : ((2 / 3 : ℝ) ^ k) ^ 2 = (4 / 9 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have hexp : ((2 / 3 : ℝ) ^ k * ε) ^ 2 = (4 / 9 : ℝ) ^ k * ε ^ 2 := by
    rw [mul_pow, hpow]
  have hexp2 : ((2 / 3 : ℝ) ^ k * ε / 3) ^ 2 = (4 / 9 : ℝ) ^ k * ε ^ 2 / 9 := by
    rw [div_pow, mul_pow, hpow]; norm_num
  rw [hexp, hexp2]
  ring

/-- **Surplus Conservation Theorem:**
Across all cascade rounds `k ≥ 0`, the total profit extracted by triangular arbitrage plus
support restorations sums to `D * ε^2 / 2`, identically equal to single-hop direct arbitrage
profit `directProfit D ε (D * ε)`. -/
theorem cascade_total_profit_hasSum {D : ℝ} (hD : D ≠ 0) (ε : ℝ) :
    HasSum (cascadeRoundProfit D ε) (D * ε ^ 2 / 2) := by
  have hgeom : HasSum (fun k : ℕ => (4 / 9 : ℝ) ^ k) (1 - (4 / 9 : ℝ))⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hscaled := hgeom.mul_left ((5 / 18 : ℝ) * D * ε ^ 2)
  have hval : (5 / 18 : ℝ) * D * ε ^ 2 * (1 - (4 / 9 : ℝ))⁻¹ = D * ε ^ 2 / 2 := by
    norm_num; ring
  rw [hval] at hscaled
  exact hscaled.congr_fun fun k => cascadeRoundProfit_closed hD ε k

theorem cascade_total_profit_eq_direct {D : ℝ} (hD : D ≠ 0) (ε : ℝ) :
    ∑' k, cascadeRoundProfit D ε k = directProfit D ε (D * ε) := by
  rw [(cascade_total_profit_hasSum hD ε).tsum_eq, directProfit_opt_val hD]

end SurplusConservation

section ArbitraryExecutions

/-- An arbitrary signed swap leg on pool `{x, y}` (with `x ≠ y`) of signed size `q`, executed by
any arbitrageur or router in any order. -/
structure SwapLeg {M : ℕ} (m : Fin M → ℕ) where
  x : Asset m
  y : Asset m
  hne : x ≠ y
  q : ℝ

/-- Initial antisymmetric residual matrix induced by external log-price shock vector `u`. -/
def initRes {M : ℕ} (m : Fin M → ℕ) (u : Fin M → ℝ) : Asset m → Asset m → ℝ :=
  fun x y => u x.1 - u y.1

/-- Effect of a single signed swap leg `(x, y, q)` on the residual matrix of equal-depth `D`
pools: moves `res x y` by `-q / D` and `res y x` by `+q / D`, leaving all other edges unchanged. -/
noncomputable def applySwap {M : ℕ} {m : Fin M → ℕ} (D : ℝ) (res : Asset m → Asset m → ℝ)
    (leg : SwapLeg m) : Asset m → Asset m → ℝ :=
  fun p q =>
    if p = leg.x ∧ q = leg.y then res p q - leg.q / D
    else if p = leg.y ∧ q = leg.x then res p q + leg.q / D
    else res p q

/-- Apply an arbitrary list of swap legs in sequence. -/
noncomputable def applySwaps {M : ℕ} {m : Fin M → ℕ} (D : ℝ) :
    (Asset m → Asset m → ℝ) → List (SwapLeg m) → (Asset m → Asset m → ℝ)
  | res, [] => res
  | res, leg :: rest => applySwaps D (applySwap D res leg) rest

/-- Aggregate unsigned pool turnover of an arbitrary execution trace `σ`. -/
def traceVol {M : ℕ} {m : Fin M → ℕ} (σ : List (SwapLeg m)) : ℝ :=
  (σ.map (fun leg => |leg.q|)).sum

/-- Total wrapped-asset interface volume touched across all pool swaps in `σ`:
each leg on `{x, y}` moves `|q|` of `x` (if wrapped) and `|q|` of `y` (if wrapped). -/
def wrappedInterfaceFlow {M : ℕ} {m : Fin M → ℕ} (σ : List (SwapLeg m)) : ℝ :=
  (σ.map (fun leg => (wrappedCount2 leg.x leg.y : ℝ) * |leg.q|)).sum

/-- Unsigned volume accumulated on a specific unordered pool `{a, b}` during trace `σ`. -/
def edgeVol {M : ℕ} {m : Fin M → ℕ} (σ : List (SwapLeg m)) (a b : Asset m) : ℝ :=
  (σ.map (fun leg =>
    if (leg.x = a ∧ leg.y = b) ∨ (leg.x = b ∧ leg.y = a) then |leg.q| else 0)).sum

/-- Core edge net-flow bound: on any distinct pair `(a, b)`, moving residual from `res a b` to
`res' a b` across ANY swap sequence `σ` requires unsigned volume on `{a, b}` of at least
`D * |res a b - res' a b|`. -/
theorem edgeVol_ge_residual_change {M : ℕ} {m : Fin M → ℕ} {D : ℝ} (hD : 0 < D)
    (res : Asset m → Asset m → ℝ) (σ : List (SwapLeg m)) (a b : Asset m) :
    D * |res a b - applySwaps D res σ a b| ≤ edgeVol σ a b := by
  induction σ generalizing res with
  | nil =>
    simp [applySwaps, edgeVol]
  | cons leg rest ih =>
    have hstep : D * |res a b - applySwap D res leg a b| ≤
        (if (leg.x = a ∧ leg.y = b) ∨ (leg.x = b ∧ leg.y = a) then |leg.q| else 0) := by
      unfold applySwap
      by_cases h1 : a = leg.x ∧ b = leg.y
      · rcases h1 with ⟨rfl, rfl⟩
        simp only [and_self, ↓reduceIte, true_or]
        have hsub : res leg.x leg.y - (res leg.x leg.y - leg.q / D) = leg.q / D := by ring
        rw [hsub, abs_div, abs_of_pos hD, mul_div_cancel₀ _ hD.ne']
      · by_cases h2 : a = leg.y ∧ b = leg.x
        · rcases h2 with ⟨rfl, rfl⟩
          have hne' : ¬ (leg.y = leg.x ∧ leg.x = leg.y) := fun h => leg.hne h.1.symm
          simp only [hne', ↓reduceIte, and_self, or_true]
          have hsub : res leg.y leg.x - (res leg.y leg.x + leg.q / D) = -(leg.q / D) := by ring
          rw [hsub, abs_neg, abs_div, abs_of_pos hD, mul_div_cancel₀ _ hD.ne']
        · have hdisj : ¬ ((leg.x = a ∧ leg.y = b) ∨ (leg.x = b ∧ leg.y = a)) := by
            rintro (⟨h1a, h1b⟩ | ⟨h2a, h2b⟩)
            · exact h1 ⟨h1a.symm, h1b.symm⟩
            · exact h2 ⟨h2b.symm, h2a.symm⟩
          simp [h1, h2, hdisj]
    have hrest := ih (applySwap D res leg)
    have htri : |res a b - applySwaps D res (leg :: rest) a b| ≤
        |res a b - applySwap D res leg a b| +
        |applySwap D res leg a b - applySwaps D (applySwap D res leg) rest a b| := by
      simpa [applySwaps] using abs_sub_le (res a b) (applySwap D res leg a b)
        (applySwaps D (applySwap D res leg) rest a b)
    have hmul : D * |res a b - applySwaps D res (leg :: rest) a b| ≤
        D * |res a b - applySwap D res leg a b| +
        D * |applySwap D res leg a b - applySwaps D (applySwap D res leg) rest a b| := by
      have := mul_le_mul_of_nonneg_left htri hD.le
      linarith
    simp only [edgeVol, List.map_cons, List.sum_cons] at hrest ⊢
    linarith

/-- If an arbitrary execution `σ` leaves edge `{a, b}` within rational stopping hurdle `δ ≥ 0`
(`|res_final a b| ≤ δ`), then unsigned volume on `{a, b}` is at least
`D * max (|u a.1 - u b.1| - δ) 0`. -/
theorem edgeVol_ge_of_equilibrium {M : ℕ} {m : Fin M → ℕ} {D δ : ℝ} (hD : 0 < D)
    (u : Fin M → ℝ) (σ : List (SwapLeg m)) (a b : Asset m)
    (heq : |applySwaps D (initRes m u) σ a b| ≤ δ) :
    D * max (|u a.1 - u b.1| - δ) 0 ≤ edgeVol σ a b := by
  have hbase := edgeVol_ge_residual_change hD (initRes m u) σ a b
  have hrev : |u a.1 - u b.1| - |applySwaps D (initRes m u) σ a b| ≤
      |initRes m u a b - applySwaps D (initRes m u) σ a b| := by
    simpa [initRes] using abs_sub_abs_le_abs_sub (u a.1 - u b.1) (applySwaps D (initRes m u) σ a b)
  have hnonneg : 0 ≤ edgeVol σ a b := by
    unfold edgeVol
    exact List.sum_nonneg fun x hx => by
      simp only [List.mem_map] at hx
      rcases hx with ⟨leg, _, rfl⟩
      split_ifs <;> positivity
  have hsub : |u a.1 - u b.1| - δ ≤ |initRes m u a b - applySwaps D (initRes m u) σ a b| := by
    linarith
  rcases le_total 0 (|u a.1 - u b.1| - δ) with hpos | hneg
  · rw [max_eq_left hpos]
    calc D * (|u a.1 - u b.1| - δ)
        ≤ D * |initRes m u a b - applySwaps D (initRes m u) σ a b| :=
          mul_le_mul_of_nonneg_left hsub hD.le
      _ ≤ edgeVol σ a b := hbase
  · rw [max_eq_right hneg, mul_zero]
    exact hnonneg

/-- Finite set of all ordered cross-family asset pairs `(x, y)` with `x.1 < y.1`. -/
def crossAssetPairs {M : ℕ} (m : Fin M → ℕ) : Finset (Asset m × Asset m) :=
  Finset.univ.filter (fun p => p.1.1 < p.2.1)

/-- Each swap leg belongs to at most one unordered cross-family pair in `crossAssetPairs m`,
so summing `edgeVol σ` over `crossAssetPairs m` never double-counts any leg. -/
private theorem sum_crossAssetPairs_edgeVol_le_traceVol {M : ℕ} (m : Fin M → ℕ)
    (σ : List (SwapLeg m)) :
    ∑ p ∈ crossAssetPairs m, edgeVol σ p.1 p.2 ≤ traceVol σ := by
  induction σ with
  | nil => simp [edgeVol, traceVol]
  | cons leg rest ih =>
    simp only [edgeVol, traceVol, List.map_cons, List.sum_cons, Finset.sum_add_distrib] at ih ⊢
    have hleg : ∑ p ∈ crossAssetPairs m,
        (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) ≤
        |leg.q| := by
      by_cases hlt : leg.x.1 < leg.y.1
      · have hmem : (leg.x, leg.y) ∈ crossAssetPairs m := by
          simp [crossAssetPairs, hlt]
        have huniq : ∀ p ∈ crossAssetPairs m, p ≠ (leg.x, leg.y) →
            (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) = 0 := by
          intro p hp hne
          have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact hne (Prod.ext h1.symm h2.symm)
            · have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
              rw [← h2, ← h1] at hp_lt
              exact lt_asymm hlt hp_lt
          simp [hneg]
        rw [Finset.sum_eq_single (leg.x, leg.y) huniq (fun h => (h hmem).elim)]
        simp
      · by_cases hgt : leg.y.1 < leg.x.1
        · have hmem : (leg.y, leg.x) ∈ crossAssetPairs m := by
            simp [crossAssetPairs, hgt]
          have huniq : ∀ p ∈ crossAssetPairs m, p ≠ (leg.y, leg.x) →
              (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) = 0 := by
            intro p hp hne
            have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
                rw [← h1, ← h2] at hp_lt
                exact lt_asymm hgt hp_lt
              · exact hne (Prod.ext h2.symm h1.symm)
            simp [hneg]
          rw [Finset.sum_eq_single (leg.y, leg.x) huniq (fun h => (h hmem).elim)]
          simp
        · have hzero : ∀ p ∈ crossAssetPairs m,
              (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) = 0 := by
            intro p hp
            have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
            have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · rw [← h1, ← h2] at hp_lt; exact hlt hp_lt
              · rw [← h2, ← h1] at hp_lt; exact hgt hp_lt
            simp [hneg]
          rw [Finset.sum_eq_zero hzero]
          exact abs_nonneg leg.q
    linarith

private theorem sum_crossAssetPairs_weighted_le_interface {M : ℕ} (m : Fin M → ℕ)
    (σ : List (SwapLeg m)) :
    ∑ p ∈ crossAssetPairs m, (wrappedCount2 p.1 p.2 : ℝ) * edgeVol σ p.1 p.2 ≤
      wrappedInterfaceFlow σ := by
  induction σ with
  | nil => simp [edgeVol, wrappedInterfaceFlow]
  | cons leg rest ih =>
    simp only [edgeVol, wrappedInterfaceFlow, List.map_cons, List.sum_cons, mul_add,
      Finset.sum_add_distrib] at ih ⊢
    have hcomm : wrappedCount2 leg.y leg.x = wrappedCount2 leg.x leg.y := by
      unfold wrappedCount2; omega
    have hleg : ∑ p ∈ crossAssetPairs m,
        (wrappedCount2 p.1 p.2 : ℝ) *
          (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) ≤
        (wrappedCount2 leg.x leg.y : ℝ) * |leg.q| := by
      by_cases hlt : leg.x.1 < leg.y.1
      · have hmem : (leg.x, leg.y) ∈ crossAssetPairs m := by simp [crossAssetPairs, hlt]
        have huniq : ∀ p ∈ crossAssetPairs m, p ≠ (leg.x, leg.y) →
            (wrappedCount2 p.1 p.2 : ℝ) *
              (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) = 0 := by
          intro p hp hne
          have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
            rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact hne (Prod.ext h1.symm h2.symm)
            · have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
              rw [← h2, ← h1] at hp_lt; exact lt_asymm hlt hp_lt
          simp [hneg]
        rw [Finset.sum_eq_single (leg.x, leg.y) huniq (fun h => (h hmem).elim)]
        simp
      · by_cases hgt : leg.y.1 < leg.x.1
        · have hmem : (leg.y, leg.x) ∈ crossAssetPairs m := by simp [crossAssetPairs, hgt]
          have huniq : ∀ p ∈ crossAssetPairs m, p ≠ (leg.y, leg.x) →
              (wrappedCount2 p.1 p.2 : ℝ) *
                (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) = 0 := by
            intro p hp hne
            have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
                rw [← h1, ← h2] at hp_lt; exact lt_asymm hgt hp_lt
              · exact hne (Prod.ext h2.symm h1.symm)
            simp [hneg]
          rw [Finset.sum_eq_single (leg.y, leg.x) huniq (fun h => (h hmem).elim)]
          simp [hcomm]
        · have hzero : ∀ p ∈ crossAssetPairs m,
              (wrappedCount2 p.1 p.2 : ℝ) *
                (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then |leg.q| else 0) = 0 := by
            intro p hp
            have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
            have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · rw [← h1, ← h2] at hp_lt; exact hlt hp_lt
              · rw [← h2, ← h1] at hp_lt; exact hgt hp_lt
            simp [hneg]
          rw [Finset.sum_eq_zero hzero]
          positivity
    linarith

/-- Grouping `crossAssetPairs m` by family pair `(a, b)` with `a < b`. -/
private theorem sum_crossAssetPairs_grouped {M : ℕ} (m : Fin M → ℕ)
    (g : Asset m → Asset m → ℝ) :
    ∑ p ∈ crossAssetPairs m, g p.1 p.2 =
      ∑ ab ∈ unorderedPairs M,
        ∑ i : Fin (m ab.1), ∑ j : Fin (m ab.2), g ⟨ab.1, i⟩ ⟨ab.2, j⟩ := by
  let fiber : Fin M × Fin M → Finset (Asset m × Asset m) := fun ab =>
    Finset.univ.image (fun ij : Fin (m ab.1) × Fin (m ab.2) => (⟨ab.1, ij.1⟩, ⟨ab.2, ij.2⟩))
  have hpart : crossAssetPairs m = (unorderedPairs M).biUnion fiber := by
    ext ⟨⟨a, i⟩, ⟨b, j⟩⟩
    simp only [crossAssetPairs, unorderedPairs, fiber, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hlt
      exact ⟨(a, b), hlt, (i, j), rfl⟩
    · rintro ⟨⟨a', b'⟩, hlt, ⟨i', j'⟩, heq⟩
      have h1 : a' = a := congrArg (fun x => x.1.1) heq
      have h2 : b' = b := congrArg (fun x => x.2.1) heq
      subst h1; subst h2; exact hlt
  have hdisj : Set.PairwiseDisjoint (unorderedPairs M : Set (Fin M × Fin M)) fiber := by
    intro ab₁ _ ab₂ _ hne
    change Disjoint (fiber ab₁) (fiber ab₂)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [fiber, Finset.mem_image, Finset.mem_univ, true_and] at hp1 hp2
    rcases hp1 with ⟨ij₁, rfl⟩
    rcases hp2 with ⟨ij₂, heq⟩
    have h1 : ab₂.1 = ab₁.1 := congrArg (fun x => x.1.1) heq
    have h2 : ab₂.2 = ab₁.2 := congrArg (fun x => x.2.1) heq
    exact hne (Prod.ext h1.symm h2.symm)
  rw [hpart, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun ab _ => ?_
  have hinj : Function.Injective
      (fun ij : Fin (m ab.1) × Fin (m ab.2) => ((⟨ab.1, ij.1⟩, ⟨ab.2, ij.2⟩) : Asset m × Asset m)) := by
    intro ij₁ ij₂ h
    have h1 : ij₁.1 = ij₂.1 := by
      have := congrArg Prod.fst h; simpa using this
    have h2 : ij₁.2 = ij₂.2 := by
      have := congrArg Prod.snd h; simpa using this
    exact Prod.ext h1 h2
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h), Fintype.sum_prod_type]

private theorem sum_isWrapped_fin {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a) (a : Fin M) :
    ∑ i : Fin (m a), (if isWrapped (⟨a, i⟩ : Asset m) then (1 : ℝ) else 0) = (m a : ℝ) - 1 := by
  have hpos := hm a
  have h0 : (⟨0, hpos⟩ : Fin (m a)) ∈ (Finset.univ : Finset (Fin (m a))) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ h0]
  have hz : (if isWrapped (⟨a, ⟨0, hpos⟩⟩ : Asset m) then (1 : ℝ) else 0) = 0 := by
    simp [isWrapped]
  have hrest : ∀ i ∈ Finset.univ.erase (⟨0, hpos⟩ : Fin (m a)),
      (if isWrapped (⟨a, i⟩ : Asset m) then (1 : ℝ) else 0) = 1 := by
    intro i hi
    have hne : i.val ≠ 0 := fun hv => (Finset.mem_erase.mp hi).1 (Fin.ext hv)
    simp [isWrapped, hne]
  rw [hz, zero_add, Finset.sum_congr rfl hrest, Finset.sum_const,
    Finset.card_erase_of_mem h0, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_sub hpos, Nat.cast_one]

/-- **Universal Routing-Independent Pool Volume Lower Bound:**
For **any** execution trace `σ` (any mix of direct trades, triangles, multi-hop routes, or
competing MEV bots in any order) that brings every cross-family pool to within stopping hurdle
`δ ≥ 0` (`|res_final| ≤ δ`), total pool turnover satisfies:
`traceVol σ ≥ D * ∑_{a<b} m_a m_b * max (|u_a - u_b| - δ) 0`. -/
theorem any_equilibrium_vol_ge {M : ℕ} (m : Fin M → ℕ) {D δ : ℝ} (hD : 0 < D)
    (u : Fin M → ℝ) (σ : List (SwapLeg m))
    (heq : ∀ x y : Asset m, x.1 < y.1 → |applySwaps D (initRes m u) σ x y| ≤ δ) :
    D * ∑ p ∈ unorderedPairs M,
        (m p.1 : ℝ) * (m p.2 : ℝ) * max (|u p.1 - u p.2| - δ) 0 ≤
      traceVol σ := by
  have h1 := sum_crossAssetPairs_edgeVol_le_traceVol m σ
  have h2 : ∑ p ∈ crossAssetPairs m, D * max (|u p.1.1 - u p.2.1| - δ) 0 ≤
      ∑ p ∈ crossAssetPairs m, edgeVol σ p.1 p.2 := by
    refine Finset.sum_le_sum fun p hp => ?_
    exact edgeVol_ge_of_equilibrium hD u σ p.1 p.2 (heq p.1 p.2 (Finset.mem_filter.mp hp).2)
  have h3 : ∑ p ∈ crossAssetPairs m, D * max (|u p.1.1 - u p.2.1| - δ) 0 =
      D * ∑ ab ∈ unorderedPairs M,
        (m ab.1 : ℝ) * (m ab.2 : ℝ) * max (|u ab.1 - u ab.2| - δ) 0 := by
    rw [sum_crossAssetPairs_grouped m (fun x y => D * max (|u x.1 - u y.1| - δ) 0),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  linarith

/-- **Universal Routing-Independent Wrapped-Interface Lower Bound:**
Under the same `δ`-no-arbitrage equilibrium condition on **any** execution trace `σ`,
total wrapped-asset pool-interface volume satisfies:
`wrappedInterfaceFlow σ ≥ D * ∑_{a<b} (2 m_a m_b - m_a - m_b) * max (|u_a - u_b| - δ) 0`. -/
theorem any_equilibrium_interface_ge {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    {D δ : ℝ} (hD : 0 < D) (u : Fin M → ℝ) (σ : List (SwapLeg m))
    (heq : ∀ x y : Asset m, x.1 < y.1 → |applySwaps D (initRes m u) σ x y| ≤ δ) :
    D * ∑ p ∈ unorderedPairs M,
        (2 * (m p.1 : ℝ) * (m p.2 : ℝ) - (m p.1 : ℝ) - (m p.2 : ℝ)) *
          max (|u p.1 - u p.2| - δ) 0 ≤
      wrappedInterfaceFlow σ := by
  have h1 := sum_crossAssetPairs_weighted_le_interface m σ
  have h2 : ∑ p ∈ crossAssetPairs m,
        (wrappedCount2 p.1 p.2 : ℝ) * (D * max (|u p.1.1 - u p.2.1| - δ) 0) ≤
      ∑ p ∈ crossAssetPairs m, (wrappedCount2 p.1 p.2 : ℝ) * edgeVol σ p.1 p.2 := by
    refine Finset.sum_le_sum fun p hp => ?_
    exact mul_le_mul_of_nonneg_left
      (edgeVol_ge_of_equilibrium hD u σ p.1 p.2 (heq p.1 p.2 (Finset.mem_filter.mp hp).2))
      (Nat.cast_nonneg _)
  have h3 : ∑ p ∈ crossAssetPairs m,
        (wrappedCount2 p.1 p.2 : ℝ) * (D * max (|u p.1.1 - u p.2.1| - δ) 0) =
      D * ∑ ab ∈ unorderedPairs M,
        (2 * (m ab.1 : ℝ) * (m ab.2 : ℝ) - (m ab.1 : ℝ) - (m ab.2 : ℝ)) *
          max (|u ab.1 - u ab.2| - δ) 0 := by
    rw [sum_crossAssetPairs_grouped m
      (fun x y => (wrappedCount2 x y : ℝ) * (D * max (|u x.1 - u y.1| - δ) 0)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    have hinner : ∀ i : Fin (m ab.1),
        ∑ j : Fin (m ab.2),
          (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ) =
        (if isWrapped (⟨ab.1, i⟩ : Asset m) then (1 : ℝ) else 0) * (m ab.2 : ℝ) +
          ((m ab.2 : ℝ) - 1) := by
      intro i
      have hexp : ∀ j : Fin (m ab.2),
          (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ) =
          (if isWrapped (⟨ab.1, i⟩ : Asset m) then (1 : ℝ) else 0) +
          (if isWrapped (⟨ab.2, j⟩ : Asset m) then (1 : ℝ) else 0) := by
        intro j; simp [wrappedCount2]
      simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, sum_isWrapped_fin m hm ab.2]
      ring
    have hsum_w :
        ∑ i : Fin (m ab.1), ∑ j : Fin (m ab.2),
          (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ) =
        2 * (m ab.1 : ℝ) * (m ab.2 : ℝ) - (m ab.1 : ℝ) - (m ab.2 : ℝ) := by
      simp_rw [hinner, Finset.sum_add_distrib, ← Finset.sum_mul, sum_isWrapped_fin m hm ab.1,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hfac :
        ∑ i : Fin (m ab.1), ∑ j : Fin (m ab.2),
          (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ) *
            (D * max (|u ab.1 - u ab.2| - δ) 0) =
        (∑ i : Fin (m ab.1), ∑ j : Fin (m ab.2),
          (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ)) *
            (D * max (|u ab.1 - u ab.2| - δ) 0) := by
      simp_rw [← Finset.sum_mul]
    rw [hfac, hsum_w]
    ring
  linarith

/-- Explicit token-transfer ledger entry: each wrapped transfer has one sender (`srcPool`,
`none` if external/mint) and one receiver (`dstPool`, `none` if external/redeem), so a single
transfer of amount `amt ≥ 0` can settle at most 2 pool interfaces. -/
structure WrappedTransfer {M : ℕ} (m : Fin M → ℕ) where
  asset : Asset m
  amt : ℝ
  hamt : 0 ≤ amt
  srcPool : Option (Asset m)
  dstPool : Option (Asset m)

/-- Total taxable wrapped-transfer volume counted once per transfer. -/
def totalTransferVol {M : ℕ} {m : Fin M → ℕ} (txs : List (WrappedTransfer m)) : ℝ :=
  (txs.map (fun t => t.amt)).sum

/-- Total pool-interface volume supplied by a list of wrapped transfers. -/
def coveredInterfaceVol {M : ℕ} {m : Fin M → ℕ} (txs : List (WrappedTransfer m)) : ℝ :=
  (txs.map (fun t =>
    (if t.srcPool.isSome then t.amt else 0) + (if t.dstPool.isSome then t.amt else 0))).sum

/-- Every transfer touches at most 2 pools (`coveredInterfaceVol txs ≤ 2 * totalTransferVol txs`). -/
theorem coveredInterfaceVol_le_two_mul {M : ℕ} {m : Fin M → ℕ}
    (txs : List (WrappedTransfer m)) :
    coveredInterfaceVol txs ≤ 2 * totalTransferVol txs := by
  induction txs with
  | nil => simp [coveredInterfaceVol, totalTransferVol]
  | cons t rest ih =>
    simp only [coveredInterfaceVol, totalTransferVol, List.map_cons, List.sum_cons, mul_add] at ih ⊢
    have h1 : (if t.srcPool.isSome then t.amt else 0) ≤ t.amt := by
      split_ifs <;> linarith [t.hamt]
    have h2 : (if t.dstPool.isSome then t.amt else 0) ≤ t.amt := by
      split_ifs <;> linarith [t.hamt]
    linarith

/-- If every transfer touches at most 1 pool (unshared transfers),
`coveredInterfaceVol txs ≤ totalTransferVol txs`. -/
theorem coveredInterfaceVol_le_unshared {M : ℕ} {m : Fin M → ℕ}
    (txs : List (WrappedTransfer m))
    (hunshared : ∀ t ∈ txs, t.srcPool.isNone ∨ t.dstPool.isNone) :
    coveredInterfaceVol txs ≤ totalTransferVol txs := by
  induction txs with
  | nil => simp [coveredInterfaceVol, totalTransferVol]
  | cons t rest ih =>
    have ht := hunshared t List.mem_cons_self
    have hrest := ih (fun s hs => hunshared s (List.mem_cons_of_mem t hs))
    simp only [coveredInterfaceVol, totalTransferVol, List.map_cons, List.sum_cons] at hrest ⊢
    have h1 : (if t.srcPool.isSome then t.amt else 0) +
        (if t.dstPool.isSome then t.amt else 0) ≤ t.amt := by
      rcases ht with hs | hd
      · have hs' : t.srcPool.isSome = false := by cases h : t.srcPool <;> simp_all
        simp only [hs', Bool.false_eq_true, ↓reduceIte, zero_add]
        split_ifs <;> linarith [t.hamt]
      · have hd' : t.dstPool.isSome = false := by cases h : t.dstPool <;> simp_all
        simp only [hd', Bool.false_eq_true, ↓reduceIte, add_zero]
        split_ifs <;> linarith [t.hamt]
    linarith

/-- **Universal Taxable Burn-Volume Lower Bound (With Arbitrary Transfer Sharing):**
For **any** `δ`-no-arbitrage clearing trace `σ` and **any** transfer realization `txs` covering
its wrapped pool interfaces (even an adversarial router maximizing pool-to-pool transfer sharing):
`totalTransferVol txs ≥ (D / 2) * ∑_{a<b} (2 m_a m_b - m_a - m_b) * max (|u_a - u_b| - δ) 0`. -/
theorem any_equilibrium_taxVol_ge_shared {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    {D δ : ℝ} (hD : 0 < D) (u : Fin M → ℝ) (σ : List (SwapLeg m))
    (txs : List (WrappedTransfer m))
    (hcover : wrappedInterfaceFlow σ ≤ coveredInterfaceVol txs)
    (heq : ∀ x y : Asset m, x.1 < y.1 → |applySwaps D (initRes m u) σ x y| ≤ δ) :
    (D / 2) * ∑ p ∈ unorderedPairs M,
        (2 * (m p.1 : ℝ) * (m p.2 : ℝ) - (m p.1 : ℝ) - (m p.2 : ℝ)) *
          max (|u p.1 - u p.2| - δ) 0 ≤
      totalTransferVol txs := by
  have h1 := any_equilibrium_interface_ge m hm hD u σ heq
  have h2 := coveredInterfaceVol_le_two_mul txs
  linarith

/-- **Equal-Family Exact Equilibrium Floor (`δ = 0`, arbitrary routing + arbitrary sharing):**
Every no-arbitrage clearing execution on `M` equal-size families (`m = n + 1`, `D = κ L`)
generates at least `n (n + 1) κ L S_M` taxable wrapped volume (`1/4` of the cascade schedule,
or `2 n (n + 1) κ L S_M = 1/2` of the cascade schedule when transfers are unshared). -/
theorem any_equilibrium_equal_taxVol_floor {M n : ℕ} {κ L : ℝ} (hD : 0 < κ * L)
    (u : Fin M → ℝ) (σ : List (SwapLeg (fun _ : Fin M => n + 1)))
    (txs : List (WrappedTransfer (fun _ : Fin M => n + 1)))
    (hcover : wrappedInterfaceFlow σ ≤ coveredInterfaceVol txs)
    (heq : ∀ x y : Asset (fun _ : Fin M => n + 1),
      x.1 < y.1 → applySwaps (κ * L) (initRes _ u) σ x y = 0) :
    (n : ℝ) * ((n : ℝ) + 1) * κ * L * totalShock u ≤ totalTransferVol txs := by
  have heq0 : ∀ x y : Asset (fun _ : Fin M => n + 1),
      x.1 < y.1 → |applySwaps (κ * L) (initRes _ u) σ x y| ≤ 0 := by
    intro x y hxy; rw [heq x y hxy, abs_zero]
  have h := any_equilibrium_taxVol_ge_shared (fun _ : Fin M => n + 1)
    (fun _ => Nat.succ_pos n) hD u σ txs hcover heq0
  have hsimp : (κ * L / 2) * ∑ p ∈ unorderedPairs M,
      (2 * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) *
        max (|u p.1 - u p.2| - 0) 0 =
      (n : ℝ) * ((n : ℝ) + 1) * κ * L * totalShock u := by
    unfold totalShock
    have hterm : ∀ p ∈ unorderedPairs M,
        (2 * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) *
          max (|u p.1 - u p.2| - 0) 0 =
        (2 * (n : ℝ) * ((n : ℝ) + 1)) * |u p.1 - u p.2| := by
      intro p _
      rw [sub_zero, max_eq_left (abs_nonneg _)]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    ring
  linarith

/-- Unshared version: when each wrapped transfer touches at most 1 pool, every no-arbitrage
clearing execution generates at least `2 n (n + 1) κ L S_M` taxable wrapped volume
(matching the direct-correction baseline). -/
theorem any_equilibrium_equal_taxVol_unshared {M n : ℕ} {κ L : ℝ} (hD : 0 < κ * L)
    (u : Fin M → ℝ) (σ : List (SwapLeg (fun _ : Fin M => n + 1)))
    (txs : List (WrappedTransfer (fun _ : Fin M => n + 1)))
    (hcover : wrappedInterfaceFlow σ ≤ coveredInterfaceVol txs)
    (hunshared : ∀ t ∈ txs, t.srcPool.isNone ∨ t.dstPool.isNone)
    (heq : ∀ x y : Asset (fun _ : Fin M => n + 1),
      x.1 < y.1 → applySwaps (κ * L) (initRes _ u) σ x y = 0) :
    2 * (n : ℝ) * ((n : ℝ) + 1) * κ * L * totalShock u ≤ totalTransferVol txs := by
  have heq0 : ∀ x y : Asset (fun _ : Fin M => n + 1),
      x.1 < y.1 → |applySwaps (κ * L) (initRes _ u) σ x y| ≤ 0 := by
    intro x y hxy; rw [heq x y hxy, abs_zero]
  have h1 := any_equilibrium_interface_ge (fun _ : Fin M => n + 1)
    (fun _ => Nat.succ_pos n) hD u σ heq0
  have h2 := coveredInterfaceVol_le_unshared txs hunshared
  have hsimp : (κ * L) * ∑ p ∈ unorderedPairs M,
      (2 * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) *
        max (|u p.1 - u p.2| - 0) 0 =
      2 * (n : ℝ) * ((n : ℝ) + 1) * κ * L * totalShock u := by
    unfold totalShock
    have hterm : ∀ p ∈ unorderedPairs M,
        (2 * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) *
          max (|u p.1 - u p.2| - 0) 0 =
        (2 * (n : ℝ) * ((n : ℝ) + 1)) * |u p.1 - u p.2| := by
      intro p _
      rw [sub_zero, max_eq_left (abs_nonneg _)]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    ring
  linarith

end ArbitraryExecutions

section RoutingIndependentYieldFloor

/-- Universal routing-independent leading gross burn yield floor (with arbitrary transfer
sharing): `Y_floor(M) = f κ n μ (M - 1) / (M (n + 1) - 1) = (1/4) Y_cascade(M)`. -/
noncomputable def yieldFloorFixedMu (f κ : ℝ) (n : ℕ) (μ : ℝ) (M : ℕ) : ℝ :=
  f * κ * (n : ℝ) * μ * ((M : ℝ) - 1) / ((M : ℝ) * ((n : ℝ) + 1) - 1)

theorem yieldFloor_eq_quarter_cascade (f κ μ : ℝ) (n M : ℕ) :
    yieldFloorFixedMu f κ n μ M = yieldFixedMu f κ n μ M / 4 := by
  unfold yieldFloorFixedMu yieldFixedMu
  ring

/-- **Routing-Independent Increasing Yield Theorem:**
Even under the worst-case burn-minimizing no-arbitrage equilibrium (arbitrary routes, arbitrary
order, maximal transfer sharing), the leading gross burn yield floor satisfies:
1. Every clearing execution achieves `f * T(txs) / K_pool ≥ yieldFloorFixedMu f κ n μ_M M`.
2. Holding `μ > 0` fixed (`n ≥ 1, f, κ > 0`), `yieldFloorFixedMu` is **strictly increasing**
   in `M ≥ 2`.
3. `yieldFloorFixedMu` converges to `f κ n μ / (n + 1) > 0` as `M → ∞`. -/
theorem any_equilibrium_yield_ge_floor {M n : ℕ} (hM : 2 ≤ M)
    {f κ L : ℝ} (hf : 0 ≤ f) (hκ : 0 < κ) (hL : 0 < L)
    (u : Fin M → ℝ) (σ : List (SwapLeg (fun _ : Fin M => n + 1)))
    (txs : List (WrappedTransfer (fun _ : Fin M => n + 1)))
    (hcover : wrappedInterfaceFlow σ ≤ coveredInterfaceVol txs)
    (heq : ∀ x y : Asset (fun _ : Fin M => n + 1),
      x.1 < y.1 → applySwaps (κ * L) (initRes _ u) σ x y = 0) :
    yieldFloorFixedMu f κ n (meanPairwiseShock u) M ≤
      f * totalTransferVol txs / poolCapital L M n := by
  have hT := any_equilibrium_equal_taxVol_floor (mul_pos hκ hL) u σ txs hcover heq
  have hKpos : 0 < poolCapital L M n := by
    unfold poolCapital poolCountReal
    have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : 0 < (M : ℝ) * ((n : ℝ) + 1) - 1 := by nlinarith
    positivity
  have hfloor_eq : yieldFloorFixedMu f κ n (meanPairwiseShock u) M =
      f * ((n : ℝ) * ((n : ℝ) + 1) * κ * L * totalShock u) / poolCapital L M n := by
    rw [yieldFloor_eq_quarter_cascade, ← grossYield_eq_yieldFixedMu hM hL.ne' u]
    unfold grossYield leadingBurn
    ring
  rw [hfloor_eq]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT hf) hKpos.le

theorem yieldFloor_step_pos {M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n)
    {f κ μ : ℝ} (hf : 0 < f) (hκ : 0 < κ) (hμ : 0 < μ) :
    0 < yieldFloorFixedMu f κ n μ (M + 1) - yieldFloorFixedMu f κ n μ M := by
  rw [yieldFloor_eq_quarter_cascade, yieldFloor_eq_quarter_cascade, ← sub_div]
  have hpos := yieldFixedMu_step_pos hM hn hf hκ hμ
  linarith

theorem yieldFloor_tendsto (f κ μ : ℝ) (n : ℕ) :
    Filter.Tendsto (fun M : ℕ => yieldFloorFixedMu f κ n μ M)
      Filter.atTop (nhds (f * κ * (n : ℝ) * μ / ((n : ℝ) + 1))) := by
  have h := (yieldFixedMu_tendsto f κ μ n).div_const 4
  have hlim : 4 * f * κ * (n : ℝ) * μ / ((n : ℝ) + 1) / 4 =
      f * κ * (n : ℝ) * μ / ((n : ℝ) + 1) := by ring
  rw [hlim] at h
  exact h.congr fun M => (yieldFloor_eq_quarter_cascade f κ μ n M).symm

end RoutingIndependentYieldFloor

end Cascades
