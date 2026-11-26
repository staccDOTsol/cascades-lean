import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Cascades.GraphSchedule

/-!
# Sections 3, 4, & 5: Yield Scaling, Limits, Evenly-Spaced Shocks, Family Addition, and Tables

Formalizes all remaining results in `cascades.md`:
* **Section 3 (Fixed mean pairwise shock `μ`):**
  * Leading gross burn yield `Y_M = 4 f κ n μ (M - 1) / (M (n + 1) - 1)`.
  * Exact step increment `Y_{M+1} - Y_M = 4 f κ n^2 μ / ((M(n+1) - 1)((M+1)(n+1) - 1)) > 0`.
  * Exact limit `Y_M → 4 f κ n μ / (n + 1)` as `M → ∞`.
  * Realizability with consistent node shocks: evenly spaced `u_a` over width
    `w_M = 3 μ (M - 1) / (M + 1) < 3 μ` achieve mean pairwise gap `μ` identically.
* **Section 4 (Fixed outer price spread `ε` & literal family addition):**
  * Evenly spaced shocks over fixed width `ε` give `S_M = ε M (M + 1) / 6` and
    `Y_M = 4 f κ n ε (M + 1) / (3 (M (n + 1) - 1))`, which is **strictly decreasing** in `M`
    and approaches `4 f κ n ε / (3 (n + 1))`.
  * Appending a new family with shock `v` adds `G(v) = ∑_a |v - u_a|` and strictly improves
    leading gross yield if and only if `G(v) > S_M (2 m M + m - 1) / (M (m M - 1))`.
* **Section 5 (Scale invariance):**
  * Scaling per-pool capital `L ↦ λ L` (`λ > 0`) leaves leading gross burn yield unchanged.
* **Tables (Sections 3 & 4):**
  * Exact rational and 3-decimal rounded verification of every row in both numerical tables.
-/

namespace Cascades

section Definitions

/-- Real-valued pool count `P(M, n) = M(n+1)(M(n+1) - 1) / 2`. -/
noncomputable def poolCountReal (M n : ℕ) : ℝ :=
  (M : ℝ) * ((n : ℝ) + 1) * ((M : ℝ) * ((n : ℝ) + 1) - 1) / 2

/-- Pool capital `K_pool = L * P`. -/
noncomputable def poolCapital (L : ℝ) (M n : ℕ) : ℝ :=
  L * poolCountReal M n

/-- Leading-order gross burn `B₁ = 4 f κ L n (n + 1) S_M`. -/
noncomputable def leadingBurn (f κ L : ℝ) (n : ℕ) (S : ℝ) : ℝ :=
  4 * f * κ * L * (n : ℝ) * ((n : ℝ) + 1) * S

/-- Leading-order gross burn yield `Y = B₁ / K_pool`. -/
noncomputable def grossYield (f κ L : ℝ) (M n : ℕ) (S : ℝ) : ℝ :=
  leadingBurn f κ L n S / poolCapital L M n

/-- Mean pairwise relative shock `μ_M = 2 S_M / (M (M - 1))`. -/
noncomputable def meanPairwiseShock {M : ℕ} (u : Fin M → ℝ) : ℝ :=
  2 * totalShock u / ((M : ℝ) * ((M : ℝ) - 1))

/-- Leading gross burn yield expressed as a function of fixed mean pairwise shock `μ`. -/
noncomputable def yieldFixedMu (f κ : ℝ) (n : ℕ) (μ : ℝ) (M : ℕ) : ℝ :=
  4 * f * κ * (n : ℝ) * μ * ((M : ℝ) - 1) / ((M : ℝ) * ((n : ℝ) + 1) - 1)

/-- Leading gross burn yield expressed as a function of fixed outer spread `ε`
(evenly spaced shocks). -/
noncomputable def yieldFixedSpread (f κ : ℝ) (n : ℕ) (ε : ℝ) (M : ℕ) : ℝ :=
  4 * f * κ * (n : ℝ) * ε * ((M : ℝ) + 1) / (3 * ((M : ℝ) * ((n : ℝ) + 1) - 1))

/-- Evenly spaced shock vector over width `w`: `u_a = (a / (M - 1)) * w`. -/
noncomputable def evenShocks (M : ℕ) (w : ℝ) (a : Fin M) : ℝ :=
  (a.val : ℝ) / ((M : ℝ) - 1) * w

/-- Width `w_M = 3 μ (M - 1) / (M + 1)` giving exact mean pairwise gap `μ`. -/
noncomputable def realizableWidth (μ : ℝ) (M : ℕ) : ℝ :=
  3 * μ * ((M : ℝ) - 1) / ((M : ℝ) + 1)

/-- Additional pairwise shock `G(v) = ∑_{a=1}^M |v - u_a|` from appending a new family
with shock `v`. -/
def addedShock {M : ℕ} (u : Fin M → ℝ) (v : ℝ) : ℝ :=
  ∑ a : Fin M, |v - u a|

end Definitions

section Section3YieldFixedMu

private lemma denom_pos {M n : ℕ} (hM : 2 ≤ M) :
    0 < (M : ℝ) * ((n : ℝ) + 1) - 1 := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- Scale invariance (Section 5): scaling per-pool liquidity `L ↦ λ L` multiplies burns and
pool capital equally and leaves leading gross yield completely unchanged. -/
theorem grossYield_scale_invariant {f κ L lam : ℝ} (hlam : lam ≠ 0)
    (M n : ℕ) (S : ℝ) :
    grossYield f κ (lam * L) M n S = grossYield f κ L M n S := by
  unfold grossYield leadingBurn poolCapital
  have hnum : 4 * f * κ * (lam * L) * (n : ℝ) * ((n : ℝ) + 1) * S =
      lam * (4 * f * κ * L * (n : ℝ) * ((n : ℝ) + 1) * S) := by ring
  have hden : lam * L * poolCountReal M n = lam * (L * poolCountReal M n) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hlam]

/-- Exact formula for `Y_M = B₁ / K_pool` in terms of `μ_M = 2 S_M / (M(M-1))`. -/
theorem grossYield_eq_yieldFixedMu {M n : ℕ} (hM : 2 ≤ M) {f κ L : ℝ} (hL : L ≠ 0)
    (u : Fin M → ℝ) :
    grossYield f κ L M n (totalShock u) = yieldFixedMu f κ n (meanPairwiseShock u) M := by
  unfold grossYield leadingBurn poolCapital poolCountReal yieldFixedMu meanPairwiseShock
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hden : (M : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 := (denom_pos hM).ne'
  field_simp [hL, hM0, hM1, hn1, hden]

/-- **Section 3 Boxed Step-Difference Identity:**
`Y_{M+1} - Y_M = 4 f κ n^2 μ / ((M(n+1) - 1)((M+1)(n+1) - 1))`. -/
theorem yieldFixedMu_step_diff {M n : ℕ} (hM : 2 ≤ M) (f κ μ : ℝ) :
    yieldFixedMu f κ n μ (M + 1) - yieldFixedMu f κ n μ M =
      4 * f * κ * (n : ℝ) ^ 2 * μ /
        (((M : ℝ) * ((n : ℝ) + 1) - 1) * (((M : ℝ) + 1) * ((n : ℝ) + 1) - 1)) := by
  unfold yieldFixedMu
  have hd1 : (M : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 := (denom_pos hM).ne'
  have hd2 : ((M : ℝ) + 1) * ((n : ℝ) + 1) - 1 ≠ 0 := by
    have := denom_pos (n := n) (M := M + 1) (by omega)
    simpa [Nat.cast_add, Nat.cast_one] using this.ne'
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [hd1, hd2]
  ring

/-- Holding `μ > 0` fixed with `n ≥ 1`, `f, κ > 0`, gross yield strictly increases with `M ≥ 2`. -/
theorem yieldFixedMu_step_pos {M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n)
    {f κ μ : ℝ} (hf : 0 < f) (hκ : 0 < κ) (hμ : 0 < μ) :
    0 < yieldFixedMu f κ n μ (M + 1) - yieldFixedMu f κ n μ M := by
  rw [yieldFixedMu_step_diff hM]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd1 : 0 < (M : ℝ) * ((n : ℝ) + 1) - 1 := denom_pos hM
  have hd2 : 0 < ((M : ℝ) + 1) * ((n : ℝ) + 1) - 1 := by
    have := denom_pos (n := n) (M := M + 1) (by omega)
    simpa [Nat.cast_add, Nat.cast_one] using this
  positivity

/-- **Section 3 Boxed Limit:** `Y_M → 4 f κ n μ / (n + 1)` as `M → ∞`. -/
theorem yieldFixedMu_tendsto (f κ μ : ℝ) (n : ℕ) :
    Filter.Tendsto (fun M : ℕ => yieldFixedMu f κ n μ M)
      Filter.atTop (nhds (4 * f * κ * (n : ℝ) * μ / ((n : ℝ) + 1))) := by
  have hinv : Filter.Tendsto (fun M : ℕ => (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Filter.Tendsto (fun M : ℕ => 1 - (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  have hden : Filter.Tendsto (fun M : ℕ => ((n : ℝ) + 1) - (1 : ℝ) / (M : ℝ))
      Filter.atTop (nhds (((n : ℝ) + 1) - 0)) :=
    tendsto_const_nhds.sub hinv
  have hne : ((n : ℝ) + 1) - 0 ≠ 0 := by rw [sub_zero]; positivity
  have hfrac : Filter.Tendsto
      (fun M : ℕ => (1 - (1 : ℝ) / (M : ℝ)) / (((n : ℝ) + 1) - (1 : ℝ) / (M : ℝ)))
      Filter.atTop (nhds ((1 - 0) / (((n : ℝ) + 1) - 0))) :=
    hnum.div hden hne
  have hscaled := hfrac.const_mul (4 * f * κ * (n : ℝ) * μ)
  have hlim : 4 * f * κ * (n : ℝ) * μ * ((1 - 0) / (((n : ℝ) + 1) - 0)) =
      4 * f * κ * (n : ℝ) * μ / ((n : ℝ) + 1) := by ring
  rw [hlim] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with M hM
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hd : (M : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 := (denom_pos hM).ne'
  have hd' : ((n : ℝ) + 1) - 1 / (M : ℝ) ≠ 0 := by
    intro h
    have : (M : ℝ) * (((n : ℝ) + 1) - 1 / (M : ℝ)) = 0 := by rw [h, mul_zero]
    have h2 : (M : ℝ) * (((n : ℝ) + 1) - 1 / (M : ℝ)) = (M : ℝ) * ((n : ℝ) + 1) - 1 := by
      field_simp [hM0]
    exact hd (h2.symm.trans this)
  unfold yieldFixedMu
  field_simp [hM0, hd, hd']

end Section3YieldFixedMu

section EvenlySpacedAndSection4

private theorem two_mul_sum_range_succ (k : ℕ) :
    2 * ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ n ihn =>
    rw [Finset.sum_range_succ, mul_add, ihn]
    ring

/-- Combinatorial identity: `6 * ∑_{0 ≤ a < b < M} (b - a) = M (M - 1) (M + 1)`. -/
private theorem sum_pair_diff_nat (M : ℕ) :
    6 * ∑ p ∈ unorderedPairs M, (p.2.val - p.1.val) = M * (M - 1) * (M + 1) := by
  induction M with
  | zero =>
    simp [unorderedPairs]
  | succ k ih =>
    -- Split `unorderedPairs (k + 1)` into pairs with `p.2 < k` and pairs with `p.2 = k`
    let f : Fin (k + 1) × Fin (k + 1) → ℕ := fun p => p.2.val - p.1.val
    let S_old : Finset (Fin (k + 1) × Fin (k + 1)) :=
      (unorderedPairs (k + 1)).filter (fun p => p.2.val < k)
    let S_new : Finset (Fin (k + 1) × Fin (k + 1)) :=
      (unorderedPairs (k + 1)).filter (fun p => ¬ p.2.val < k)
    have hsplit : ∑ p ∈ unorderedPairs (k + 1), f p =
        (∑ p ∈ S_old, f p) + (∑ p ∈ S_new, f p) := by
      rw [← Finset.sum_filter_add_sum_filter_not (unorderedPairs (k + 1)) (fun p => p.2.val < k)]
    have hold : ∑ p ∈ S_old, f p = ∑ p ∈ unorderedPairs k, (p.2.val - p.1.val) := by
      refine Finset.sum_bij (fun p hp =>
        (⟨p.1.val, lt_trans (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            (Finset.mem_filter.mp hp).2⟩,
         ⟨p.2.val, (Finset.mem_filter.mp hp).2⟩)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [unorderedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      · intro p₁ _ p₂ _ h
        have h1 : p₁.1.val = p₂.1.val := congrArg (fun x => x.1.val) h
        have h2 : p₁.2.val = p₂.2.val := congrArg (fun x => x.2.val) h
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)
      · intro q hq
        have hqlt : q.1.val < q.2.val := (Finset.mem_filter.mp hq).2
        refine ⟨(q.1.castSucc, q.2.castSucc), ?_, by ext <;> rfl⟩
        simp only [S_old, unorderedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hqlt, q.2.isLt⟩
      · intro _ _; rfl
    have hnew : ∑ p ∈ S_new, f p = ∑ i ∈ Finset.range k, (k - i) := by
      refine Finset.sum_bij (fun p _ => p.1.val) ?_ ?_ ?_ ?_
      · intro p hp
        have hp1 : p.1.val < p.2.val := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have hp2 : p.2.val = k := by
          have hge : k ≤ p.2.val := Nat.le_of_not_lt (Finset.mem_filter.mp hp).2
          have hlt : p.2.val < k + 1 := p.2.isLt
          omega
        rw [Finset.mem_range]
        omega
      · intro p₁ hp1 p₂ hp2 h
        have h21 : p₁.2.val = k := by
          have := Nat.le_of_not_lt (Finset.mem_filter.mp hp1).2; have := p₁.2.isLt; omega
        have h22 : p₂.2.val = k := by
          have := Nat.le_of_not_lt (Finset.mem_filter.mp hp2).2; have := p₂.2.isLt; omega
        exact Prod.ext (Fin.ext h) (Fin.ext (h21.trans h22.symm))
      · intro i hi
        rw [Finset.mem_range] at hi
        refine ⟨(⟨i, by omega⟩, ⟨k, Nat.lt_succ_self k⟩), ?_, rfl⟩
        simp only [S_new, unorderedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi, Nat.not_lt.mpr le_rfl⟩
      · intro p hp
        have hp2 : p.2.val = k := by
          have := Nat.le_of_not_lt (Finset.mem_filter.mp hp).2; have := p.2.isLt; omega
        simp [f, hp2]
    have htri : 2 * ∑ i ∈ Finset.range k, (k - i) = k * (k + 1) := by
      have hrev : ∑ i ∈ Finset.range k, (k - i) = ∑ i ∈ Finset.range k, (i + 1) := by
        have := Finset.sum_range_reflect (fun i => i + 1) k
        refine (Finset.sum_congr rfl fun i hi => ?_).trans this
        rw [Finset.mem_range] at hi
        omega
      rw [hrev]
      exact two_mul_sum_range_succ k
    rw [hsplit, hold, hnew, mul_add, ih]
    have h6new : 6 * ∑ i ∈ Finset.range k, (k - i) = 3 * (k * (k + 1)) := by omega
    rw [h6new]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring

/-- Exact total pairwise shock for `M` evenly spaced families over width `w ≥ 0`:
`S_M = w * M * (M + 1) / 6`. -/
theorem totalShock_evenShocks {M : ℕ} (hM : 2 ≤ M) {w : ℝ} (hw : 0 ≤ w) :
    totalShock (evenShocks M w) = w * (M : ℝ) * ((M : ℝ) + 1) / 6 := by
  unfold totalShock evenShocks
  have hM1 : 0 < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hterm : ∀ p ∈ unorderedPairs M,
      |(p.1.val : ℝ) / ((M : ℝ) - 1) * w - (p.2.val : ℝ) / ((M : ℝ) - 1) * w| =
      (w / ((M : ℝ) - 1)) * ((p.2.val - p.1.val : ℕ) : ℝ) := by
    intro p hp
    have hlt : p.1.val < p.2.val := (Finset.mem_filter.mp hp).2
    have hle : p.1.val ≤ p.2.val := hlt.le
    have hcast : ((p.2.val - p.1.val : ℕ) : ℝ) = (p.2.val : ℝ) - (p.1.val : ℝ) :=
      Nat.cast_sub hle
    rw [hcast]
    have hdiff : (p.1.val : ℝ) / ((M : ℝ) - 1) * w - (p.2.val : ℝ) / ((M : ℝ) - 1) * w =
        -(w / ((M : ℝ) - 1) * ((p.2.val : ℝ) - (p.1.val : ℝ))) := by ring
    rw [hdiff, abs_neg, abs_of_nonneg]
    have hpos : (0 : ℝ) ≤ (p.2.val : ℝ) - (p.1.val : ℝ) := by
      have : (p.1.val : ℝ) ≤ p.2.val := by exact_mod_cast hle
      linarith
    positivity
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hnat : (6 : ℝ) * (∑ p ∈ unorderedPairs M, ((p.2.val - p.1.val : ℕ) : ℝ)) =
      (M : ℝ) * ((M : ℝ) - 1) * ((M : ℝ) + 1) := by
    have h1 := congrArg (Nat.cast (R := ℝ)) (sum_pair_diff_nat M)
    have hM1nat : 1 ≤ M := by omega
    simpa [Nat.cast_sum, Nat.cast_sub hM1nat] using h1
  have hsum : (∑ p ∈ unorderedPairs M, ((p.2.val - p.1.val : ℕ) : ℝ)) =
      (M : ℝ) * ((M : ℝ) - 1) * ((M : ℝ) + 1) / 6 := by linarith
  rw [hsum]
  field_simp [hM1.ne']

/-- **Section 3 Realizability Theorem:**
Evenly spacing `M ≥ 2` shocks over width `w_M = 3 μ (M - 1) / (M + 1)` stays strictly
bounded (`w_M < 3 μ`) and realizes mean pairwise gap `μ_M = μ` identically. -/
theorem realizable_fixed_mean_shock {M : ℕ} (hM : 2 ≤ M) {μ : ℝ} (hμ : 0 < μ) :
    realizableWidth μ M < 3 * μ ∧
    meanPairwiseShock (evenShocks M (realizableWidth μ M)) = μ := by
  have hM1 : 0 < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hMp1 : 0 < (M : ℝ) + 1 := by positivity
  have hw_nonneg : 0 ≤ realizableWidth μ M := by
    unfold realizableWidth; positivity
  constructor
  · unfold realizableWidth
    rw [div_lt_iff₀ hMp1]
    nlinarith
  · unfold meanPairwiseShock
    rw [totalShock_evenShocks hM hw_nonneg]
    unfold realizableWidth
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    field_simp [hM0, hM1.ne', hMp1.ne']
    ring

/-- **Section 4 Fixed-Spread Formula:**
When `M ≥ 2` shocks are evenly spaced over a fixed spread `ε ≥ 0`,
`Y_M = 4 f κ n ε (M + 1) / (3 (M (n + 1) - 1))`. -/
theorem grossYield_fixedSpread {M n : ℕ} (hM : 2 ≤ M) {f κ L ε : ℝ}
    (hL : L ≠ 0) (hε : 0 ≤ ε) :
    grossYield f κ L M n (totalShock (evenShocks M ε)) = yieldFixedSpread f κ n ε M := by
  rw [totalShock_evenShocks hM hε]
  unfold grossYield leadingBurn poolCapital poolCountReal yieldFixedSpread
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hden : (M : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 := (denom_pos hM).ne'
  field_simp [hL, hM0, hn1, hden]
  ring

/-- **Section 4 Fixed-Spread Monotonicity Reversal:**
Under fixed outer spread `ε > 0`, gross yield **strictly decreases** with family count `M ≥ 2`. -/
theorem yieldFixedSpread_step_neg {M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n)
    {f κ ε : ℝ} (hf : 0 < f) (hκ : 0 < κ) (hε : 0 < ε) :
    yieldFixedSpread f κ n ε (M + 1) < yieldFixedSpread f κ n ε M := by
  unfold yieldFixedSpread
  have hd1 : 0 < (M : ℝ) * ((n : ℝ) + 1) - 1 := denom_pos hM
  have hd2 : 0 < ((M : ℝ) + 1) * ((n : ℝ) + 1) - 1 := by
    have := denom_pos (n := n) (M := M + 1) (by omega)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← sub_neg]
  have hdiff :
      4 * f * κ * (n : ℝ) * ε * ((M : ℝ) + 1 + 1) / (3 * (((M : ℝ) + 1) * ((n : ℝ) + 1) - 1)) -
      4 * f * κ * (n : ℝ) * ε * ((M : ℝ) + 1) / (3 * ((M : ℝ) * ((n : ℝ) + 1) - 1)) =
      -(4 * f * κ * (n : ℝ) * ε * ((n : ℝ) + 2)) /
        (3 * ((M : ℝ) * ((n : ℝ) + 1) - 1) * (((M : ℝ) + 1) * ((n : ℝ) + 1) - 1)) := by
    field_simp [hd1.ne', hd2.ne']
    ring
  rw [hdiff]
  have hnum : 0 < 4 * f * κ * (n : ℝ) * ε * ((n : ℝ) + 2) := by positivity
  have hden : 0 < 3 * ((M : ℝ) * ((n : ℝ) + 1) - 1) * (((M : ℝ) + 1) * ((n : ℝ) + 1) - 1) := by
    positivity
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hnum) hden

/-- Under fixed outer spread `ε ≥ 0`, the average pairwise shock `μ_M` declines toward `ε / 3`. -/
theorem meanPairwiseShock_evenShocks_tendsto {ε : ℝ} (hε : 0 ≤ ε) :
    Filter.Tendsto (fun M : ℕ => meanPairwiseShock (evenShocks M ε))
      Filter.atTop (nhds (ε / 3)) := by
  have hinv : Filter.Tendsto (fun M : ℕ => (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Filter.Tendsto (fun M : ℕ => 1 + (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hinv
  have hden : Filter.Tendsto (fun M : ℕ => 1 - (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  have hfrac : Filter.Tendsto
      (fun M : ℕ => (1 + (1 : ℝ) / (M : ℝ)) / (1 - (1 : ℝ) / (M : ℝ)))
      Filter.atTop (nhds ((1 + 0) / (1 - 0))) :=
    hnum.div hden (by norm_num)
  have hscaled := hfrac.const_mul (ε / 3)
  have hlim : ε / 3 * ((1 + 0) / (1 - 0)) = ε / 3 := by ring
  rw [hlim] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with M hM
  unfold meanPairwiseShock
  rw [totalShock_evenShocks hM hε]
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hd' : 1 - 1 / (M : ℝ) ≠ 0 := by
    intro h
    have : (M : ℝ) * (1 - 1 / (M : ℝ)) = 0 := by rw [h, mul_zero]
    have h2 : (M : ℝ) * (1 - 1 / (M : ℝ)) = (M : ℝ) - 1 := by field_simp [hM0]
    exact hM1 (h2.symm.trans this)
  field_simp [hM0, hM1, hd']
  ring

/-- Under fixed outer spread `ε`, `Y_M → 4 f κ n ε / (3 (n + 1))` as `M → ∞`. -/
theorem yieldFixedSpread_tendsto (f κ ε : ℝ) (n : ℕ) :
    Filter.Tendsto (fun M : ℕ => yieldFixedSpread f κ n ε M)
      Filter.atTop (nhds (4 * f * κ * (n : ℝ) * ε / (3 * ((n : ℝ) + 1)))) := by
  have hinv : Filter.Tendsto (fun M : ℕ => (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Filter.Tendsto (fun M : ℕ => 1 + (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hinv
  have hden : Filter.Tendsto (fun M : ℕ => ((n : ℝ) + 1) - (1 : ℝ) / (M : ℝ))
      Filter.atTop (nhds (((n : ℝ) + 1) - 0)) :=
    tendsto_const_nhds.sub hinv
  have hne : ((n : ℝ) + 1) - 0 ≠ 0 := by rw [sub_zero]; positivity
  have hfrac : Filter.Tendsto
      (fun M : ℕ => (1 + (1 : ℝ) / (M : ℝ)) / (((n : ℝ) + 1) - (1 : ℝ) / (M : ℝ)))
      Filter.atTop (nhds ((1 + 0) / (((n : ℝ) + 1) - 0))) :=
    hnum.div hden hne
  have hscaled := hfrac.const_mul (4 * f * κ * (n : ℝ) * ε / 3)
  have hlim : 4 * f * κ * (n : ℝ) * ε / 3 * ((1 + 0) / (((n : ℝ) + 1) - 0)) =
      4 * f * κ * (n : ℝ) * ε / (3 * ((n : ℝ) + 1)) := by
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn1]
    ring
  rw [hlim] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with M hM
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hd : (M : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 := (denom_pos hM).ne'
  have hd' : ((n : ℝ) + 1) - 1 / (M : ℝ) ≠ 0 := by
    intro h
    have : (M : ℝ) * (((n : ℝ) + 1) - 1 / (M : ℝ)) = 0 := by rw [h, mul_zero]
    have h2 : (M : ℝ) * (((n : ℝ) + 1) - 1 / (M : ℝ)) = (M : ℝ) * ((n : ℝ) + 1) - 1 := by
      field_simp [hM0]
    exact hd (h2.symm.trans this)
  unfold yieldFixedSpread
  field_simp [hM0, hd, hd']

/-- Appending a new family with shock `v` increases `S_M` by `G(v) = ∑_a |v - u_a|`. -/
theorem totalShock_snoc {M : ℕ} (u : Fin M → ℝ) (v : ℝ) :
    totalShock (Fin.snoc u v) = totalShock u + addedShock u v := by
  unfold totalShock addedShock
  let uv : Fin (M + 1) → ℝ := Fin.snoc u v
  let S_old : Finset (Fin (M + 1) × Fin (M + 1)) :=
    (unorderedPairs (M + 1)).filter (fun p => p.2.val < M)
  let S_new : Finset (Fin (M + 1) × Fin (M + 1)) :=
    (unorderedPairs (M + 1)).filter (fun p => ¬ p.2.val < M)
  have hsplit : ∑ p ∈ unorderedPairs (M + 1), |uv p.1 - uv p.2| =
      (∑ p ∈ S_old, |uv p.1 - uv p.2|) +
      (∑ p ∈ S_new, |uv p.1 - uv p.2|) := by
    rw [← Finset.sum_filter_add_sum_filter_not (unorderedPairs (M + 1)) (fun p => p.2.val < M)]
  change ∑ p ∈ unorderedPairs (M + 1), |uv p.1 - uv p.2| = _
  rw [hsplit]
  congr 1
  · refine Finset.sum_bij (fun p hp =>
      (⟨p.1.val, lt_trans (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          (Finset.mem_filter.mp hp).2⟩,
       ⟨p.2.val, (Finset.mem_filter.mp hp).2⟩)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [unorderedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    · intro p₁ _ p₂ _ h
      exact Prod.ext (Fin.ext (congrArg (fun x => x.1.val) h))
        (Fin.ext (congrArg (fun x => x.2.val) h))
    · intro q hq
      have hqlt : q.1.val < q.2.val := (Finset.mem_filter.mp hq).2
      refine ⟨(q.1.castSucc, q.2.castSucc), ?_, by ext <;> rfl⟩
      simp only [S_old, unorderedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqlt, q.2.isLt⟩
    · intro p hp
      have h2lt : p.2.val < M := (Finset.mem_filter.mp hp).2
      have h1lt : p.1.val < M := lt_trans (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2 h2lt
      have hv1 : uv p.1 = u ⟨p.1.val, h1lt⟩ := by
        conv_lhs => rw [show p.1 = Fin.castSucc ⟨p.1.val, h1lt⟩ from Fin.ext rfl]
        exact Fin.snoc_castSucc _ _ _
      have hv2 : uv p.2 = u ⟨p.2.val, h2lt⟩ := by
        conv_lhs => rw [show p.2 = Fin.castSucc ⟨p.2.val, h2lt⟩ from Fin.ext rfl]
        exact Fin.snoc_castSucc _ _ _
      rw [hv1, hv2]
  · refine Finset.sum_bij (fun p hp =>
      ⟨p.1.val, by
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have h2 := Nat.le_of_not_lt (Finset.mem_filter.mp hp).2
        have h3 := p.2.isLt
        omega⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro p₁ hp1 p₂ hp2 h
      have h1 : p₁.1.val = p₂.1.val := congrArg (Fin.val (n := M)) h
      have h21 : p₁.2.val = M := by
        have := Nat.le_of_not_lt (Finset.mem_filter.mp hp1).2; have := p₁.2.isLt; omega
      have h22 : p₂.2.val = M := by
        have := Nat.le_of_not_lt (Finset.mem_filter.mp hp2).2; have := p₂.2.isLt; omega
      exact Prod.ext (Fin.ext h1) (Fin.ext (h21.trans h22.symm))
    · intro a _
      refine ⟨(a.castSucc, Fin.last M), ?_, by ext; rfl⟩
      simp only [S_new, unorderedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a.isLt, Nat.not_lt.mpr le_rfl⟩
    · intro p hp
      have h2eq : p.2 = Fin.last M := by
        ext
        have := Nat.le_of_not_lt (Finset.mem_filter.mp hp).2
        have := p.2.isLt
        change p.2.val = M; omega
      have h1lt : p.1.val < M := by
        have hlt := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        rw [h2eq] at hlt; exact hlt
      have hv1 : uv p.1 = u ⟨p.1.val, h1lt⟩ := by
        conv_lhs => rw [show p.1 = Fin.castSucc ⟨p.1.val, h1lt⟩ from Fin.ext rfl]
        exact Fin.snoc_castSucc _ _ _
      have hv2 : uv p.2 = v := by
        rw [h2eq]
        exact Fin.snoc_last _ _
      rw [hv1, hv2, abs_sub_comm]

/-- **Section 4 Boxed Literal-Addition Criterion:**
Appending a new family with shock `v` (preserving all existing shocks `u`) strictly improves
leading gross yield if and only if
`G(v) > S_M * (2 m M + m - 1) / (M * (m M - 1))`, where `m = n + 1`. -/
theorem yield_snoc_gt_iff {M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n)
    {f κ L : ℝ} (hf : 0 < f) (hκ : 0 < κ) (hL : 0 < L)
    (u : Fin M → ℝ) (v : ℝ) :
    let m : ℝ := (n : ℝ) + 1
    grossYield f κ L (M + 1) n (totalShock (Fin.snoc u v)) >
      grossYield f κ L M n (totalShock u) ↔
    addedShock u v >
      totalShock u * (2 * m * (M : ℝ) + m - 1) / ((M : ℝ) * (m * (M : ℝ) - 1)) := by
  intro m
  rw [totalShock_snoc]
  unfold grossYield leadingBurn poolCapital poolCountReal
  have hMpos : (0 : ℝ) < M := by positivity
  have hmpos : (0 : ℝ) < m := by positivity
  have hden1 : (0 : ℝ) < (M : ℝ) * m - 1 := by simpa [m] using denom_pos (M := M) (n := n) hM
  have hden2 : (0 : ℝ) < ((M : ℝ) + 1) * m - 1 := by
    have := denom_pos (M := M + 1) (n := n) (by omega)
    simpa [m, Nat.cast_add, Nat.cast_one] using this
  have hK1 : 0 < L * ((M : ℝ) * m * ((M : ℝ) * m - 1) / 2) := by positivity
  have hK2 : 0 < L * (((M : ℝ) + 1) * m * (((M : ℝ) + 1) * m - 1) / 2) := by positivity
  have hcpos : 0 < 4 * f * κ * L * (n : ℝ) * m := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hMden : 0 < (M : ℝ) * (m * (M : ℝ) - 1) := by
    have : m * (M : ℝ) - 1 = (M : ℝ) * m - 1 := by ring
    rw [this]; positivity
  simp only [Nat.cast_add, Nat.cast_one, gt_iff_lt]
  rw [div_lt_div_iff₀ hK1 hK2, div_lt_iff₀ hMden]
  have hlhs_eq :
      4 * f * κ * L * (n : ℝ) * ((n : ℝ) + 1) * totalShock u *
        (L * (((M : ℝ) + 1) * ((n : ℝ) + 1) * (((M : ℝ) + 1) * ((n : ℝ) + 1) - 1) / 2)) <
      4 * f * κ * L * (n : ℝ) * ((n : ℝ) + 1) * (totalShock u + addedShock u v) *
        (L * ((M : ℝ) * ((n : ℝ) + 1) * ((M : ℝ) * ((n : ℝ) + 1) - 1) / 2)) ↔
      totalShock u * (((M : ℝ) + 1) * (((M : ℝ) + 1) * m - 1)) <
      (totalShock u + addedShock u v) * ((M : ℝ) * ((M : ℝ) * m - 1)) := by
    have hfac : 0 < (4 * f * κ * L * (n : ℝ) * m) * (L * m / 2) := by positivity
    have hA :
        4 * f * κ * L * (n : ℝ) * ((n : ℝ) + 1) * totalShock u *
          (L * (((M : ℝ) + 1) * ((n : ℝ) + 1) * (((M : ℝ) + 1) * ((n : ℝ) + 1) - 1) / 2)) =
        ((4 * f * κ * L * (n : ℝ) * m) * (L * m / 2)) *
          (totalShock u * (((M : ℝ) + 1) * (((M : ℝ) + 1) * m - 1))) := by
      dsimp [m]; ring
    have hB :
        4 * f * κ * L * (n : ℝ) * ((n : ℝ) + 1) * (totalShock u + addedShock u v) *
          (L * ((M : ℝ) * ((n : ℝ) + 1) * ((M : ℝ) * ((n : ℝ) + 1) - 1) / 2)) =
        ((4 * f * κ * L * (n : ℝ) * m) * (L * m / 2)) *
          ((totalShock u + addedShock u v) * ((M : ℝ) * ((M : ℝ) * m - 1))) := by
      dsimp [m]; ring
    rw [hA, hB, mul_lt_mul_iff_right₀ hfac]
  rw [hlhs_eq]
  constructor <;> intro h <;> linarith

end EvenlySpacedAndSection4

section NumericalTables

/-- **Section 3 Table Verification (`n = 2`, fixed mean pairwise shock `μ`):**
Verifies exact pool counts `P`, normalized pool capital `Capital / L₀`, normalized burns
`Burn / B₀`, and exact normalized yields `Yield / (f κ μ)` (with 3-decimal rounding error
strictly `< 0.0005` against every printed entry in `cascades.md`). -/
theorem table_section3_verified :
    -- Row M = 2, L/L₀ = 1: P = 15, Capital = 15, Burn = 24, Yield = 1.600
    (Fintype.card (Pool (fun _ : Fin 2 => 3)) = 15 ∧
      (1 : ℝ) * poolCountReal 2 2 = 15 ∧
      leadingBurn 1 1 1 2 ((2 * 1 : ℝ) / 2) = 24 ∧
      yieldFixedMu 1 1 2 1 2 = 8 / 5 ∧
      |yieldFixedMu 1 1 2 1 2 - 1.600| < 0.0005) ∧
    -- Row M = 3, L/L₀ = 2: P = 36, Capital = 72, Burn = 144, Yield = 2.000
    (Fintype.card (Pool (fun _ : Fin 3 => 3)) = 36 ∧
      (2 : ℝ) * poolCountReal 3 2 = 72 ∧
      leadingBurn 1 1 2 2 ((3 * 2 : ℝ) / 2) = 144 ∧
      yieldFixedMu 1 1 2 1 3 = 2 ∧
      |yieldFixedMu 1 1 2 1 3 - 2.000| < 0.0005) ∧
    -- Row M = 4, L/L₀ = 4: P = 66, Capital = 264, Burn = 576, Yield = 2.182 (24/11)
    (Fintype.card (Pool (fun _ : Fin 4 => 3)) = 66 ∧
      (4 : ℝ) * poolCountReal 4 2 = 264 ∧
      leadingBurn 1 1 4 2 ((4 * 3 : ℝ) / 2) = 576 ∧
      yieldFixedMu 1 1 2 1 4 = 24 / 11 ∧
      |yieldFixedMu 1 1 2 1 4 - 2.182| < 0.0005) ∧
    -- Row M = 8, L/L₀ = 8: P = 276, Capital = 2208, Burn = 5376, Yield = 2.435 (56/23)
    (Fintype.card (Pool (fun _ : Fin 8 => 3)) = 276 ∧
      (8 : ℝ) * poolCountReal 8 2 = 2208 ∧
      leadingBurn 1 1 8 2 ((8 * 7 : ℝ) / 2) = 5376 ∧
      yieldFixedMu 1 1 2 1 8 = 56 / 23 ∧
      |yieldFixedMu 1 1 2 1 8 - 2.435| < 0.0005) ∧
    -- Row M = 16, L/L₀ = 16: P = 1128, Capital = 18048, Burn = 46080, Yield = 2.553 (120/47)
    (Fintype.card (Pool (fun _ : Fin 16 => 3)) = 1128 ∧
      (16 : ℝ) * poolCountReal 16 2 = 18048 ∧
      leadingBurn 1 1 16 2 ((16 * 15 : ℝ) / 2) = 46080 ∧
      yieldFixedMu 1 1 2 1 16 = 120 / 47 ∧
      |yieldFixedMu 1 1 2 1 16 - 2.553| < 0.0005) := by
  simp only [card_pool_equal, poolCountReal, leadingBurn, yieldFixedMu]
  norm_num

/-- **Section 4 Table Verification (`n = 2`, fixed outer spread `ε`):**
Verifies exact normalized burns `Burn / B̃₀` and exact normalized yields `Yield / (f κ ε)`
(with 3-decimal rounding error strictly `< 0.0005` against every printed entry in `cascades.md`). -/
theorem table_section4_verified :
    -- Row M = 2, L/L₀ = 1: Burn = 24, Yield = 1.600 (8/5)
    (leadingBurn 1 1 1 2 (2 * 3 / 6) = 24 ∧
      yieldFixedSpread 1 1 2 1 2 = 8 / 5 ∧
      |yieldFixedSpread 1 1 2 1 2 - 1.600| < 0.0005) ∧
    -- Row M = 3, L/L₀ = 2: Burn = 96, Yield = 1.333 (4/3)
    (leadingBurn 1 1 2 2 (3 * 4 / 6) = 96 ∧
      yieldFixedSpread 1 1 2 1 3 = 4 / 3 ∧
      |yieldFixedSpread 1 1 2 1 3 - 1.333| < 0.0005) ∧
    -- Row M = 4, L/L₀ = 4: Burn = 320, Yield = 1.212 (40/33)
    (leadingBurn 1 1 4 2 (4 * 5 / 6) = 320 ∧
      yieldFixedSpread 1 1 2 1 4 = 40 / 33 ∧
      |yieldFixedSpread 1 1 2 1 4 - 1.212| < 0.0005) ∧
    -- Row M = 8, L/L₀ = 8: Burn = 2304, Yield = 1.043 (24/23)
    (leadingBurn 1 1 8 2 (8 * 9 / 6) = 2304 ∧
      yieldFixedSpread 1 1 2 1 8 = 24 / 23 ∧
      |yieldFixedSpread 1 1 2 1 8 - 1.043| < 0.0005) ∧
    -- Row M = 16, L/L₀ = 16: Burn = 17408, Yield = 0.965 (136/141)
    (leadingBurn 1 1 16 2 (16 * 17 / 6) = 17408 ∧
      yieldFixedSpread 1 1 2 1 16 = 136 / 141 ∧
      |yieldFixedSpread 1 1 2 1 16 - 0.965| < 0.0005) := by
  simp only [leadingBurn, yieldFixedSpread]
  norm_num

end NumericalTables

end Cascades
