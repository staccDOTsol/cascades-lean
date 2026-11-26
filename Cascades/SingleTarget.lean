import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# Section 1 & Result: Single-Target Triangular Arbitrage and Small-Burn Expansion

Formalizes the single-target local model from `cascades.md`:
* Triangular profit `Π(q) = r * q - 3 * q^2 / (2 * D)` and unique maximizer `q* = D * r / 3`.
* Support-restored geometric contraction `r_{k+1} = (2 / 3) * r_k` and exact series `∑' k, q_k = D * ε`.
* Per-target total pool turnover `5 * D * ε` (3 triangle + 2 corrective legs) and taxable wrapped
  turnover `2 * D * ε` (original/wrapper) and `4 * D * ε` (wrapper/wrapper).
* First-order proportional burn `B(f) = f * T₀ + O(f^2)` both in general (`T(f) = T₀ + O(f)`)
  and in an explicit threshold-stopped proportional-burn friction model.
-/

namespace Cascades

section SingleTarget

/-- Triangular arbitrage profit on a target with residual `r`, equal local depths `D`,
and trade size `q`. -/
noncomputable def triangleProfit (D r q : ℝ) : ℝ :=
  r * q - 3 * q ^ 2 / (2 * D)

/-- Profit-maximizing single-round trade size `q_k = D * r_k / 3`. -/
noncomputable def optTrade (D r : ℝ) : ℝ :=
  D * r / 3

/-- Exact completed-square identity for the triangular profit function. -/
theorem triangleProfit_eq_sub_sq {D : ℝ} (hD : D ≠ 0) (r q : ℝ) :
    triangleProfit D r q =
      D * r ^ 2 / 6 - 3 / (2 * D) * (q - optTrade D r) ^ 2 := by
  unfold triangleProfit optTrade
  field_simp [hD]
  ring

/-- Value of triangular profit at the optimal trade size `q = D * r / 3`. -/
theorem triangleProfit_opt_val {D : ℝ} (hD : D ≠ 0) (r : ℝ) :
    triangleProfit D r (optTrade D r) = D * r ^ 2 / 6 := by
  rw [triangleProfit_eq_sub_sq hD]
  ring

/-- `q = D * r / 3` globally maximizes `Π(q)` when `D > 0`. -/
theorem triangleProfit_le_opt {D : ℝ} (hD : 0 < D) (r q : ℝ) :
    triangleProfit D r q ≤ triangleProfit D r (optTrade D r) := by
  rw [triangleProfit_eq_sub_sq hD.ne', triangleProfit_opt_val hD.ne']
  have hnonneg : 0 ≤ 3 / (2 * D) * (q - optTrade D r) ^ 2 := by positivity
  linarith

/-- `q = D * r / 3` is the unique maximizer of `Π(q)` when `D > 0`. -/
theorem triangleProfit_eq_opt_iff {D : ℝ} (hD : 0 < D) (r q : ℝ) :
    triangleProfit D r q = triangleProfit D r (optTrade D r) ↔ q = optTrade D r := by
  rw [triangleProfit_eq_sub_sq hD.ne', triangleProfit_opt_val hD.ne']
  constructor
  · intro h
    have hzero : 3 / (2 * D) * (q - optTrade D r) ^ 2 = 0 := by linarith
    have hcoeff : (3 : ℝ) / (2 * D) ≠ 0 := by positivity
    have hsq : (q - optTrade D r) ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left hcoeff
    linarith [sq_eq_zero_iff.mp hsq]
  · intro h
    rw [h]
    ring

/-- Every non-zero residual yields strictly positive triangular profit when `D > 0`. -/
theorem triangleProfit_opt_pos {D r : ℝ} (hD : 0 < D) (hr : r ≠ 0) :
    0 < triangleProfit D r (optTrade D r) := by
  rw [triangleProfit_opt_val hD.ne']
  positivity

/-- Sequence of target residuals `r_k` under repeated optimal triangle trade plus
external restoration of both supports: `r_0 = ε`, `r_{k+1} = (2/3) * r_k`. -/
noncomputable def residualSeq (ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | k + 1 => (2 / 3 : ℝ) * residualSeq ε k

/-- Sequence of optimal trade sizes `q_k = D * r_k / 3`. -/
noncomputable def tradeSeq (D ε : ℝ) (k : ℕ) : ℝ :=
  optTrade D (residualSeq ε k)

/-- Restoring both supports after executing `q_k = D * r_k / 3` reduces the target residual
by `q_k / D`, giving `r_{k+1} = (2/3) * r_k`. -/
theorem residualSeq_step_from_trade {D : ℝ} (hD : D ≠ 0) (ε : ℝ) (k : ℕ) :
    residualSeq ε (k + 1) = residualSeq ε k - tradeSeq D ε k / D := by
  simp only [residualSeq, tradeSeq, optTrade]
  field_simp [hD]
  ring

/-- Closed form `r_k = (2/3)^k * ε`. -/
theorem residualSeq_closed (ε : ℝ) (k : ℕ) :
    residualSeq ε k = (2 / 3 : ℝ) ^ k * ε := by
  induction k with
  | zero => simp [residualSeq]
  | succ k ih =>
    simp only [residualSeq, ih, pow_succ']
    ring

/-- Closed form `q_k = (D * ε / 3) * (2/3)^k`. -/
theorem tradeSeq_closed (D ε : ℝ) (k : ℕ) :
    tradeSeq D ε k = (D * ε / 3) * (2 / 3 : ℝ) ^ k := by
  simp only [tradeSeq, optTrade, residualSeq_closed]
  ring

/-- Partial sum telescoping identity: after `K` rounds, total volume traded is `D * (ε - r_K)`. -/
theorem tradeSeq_partial_sum (D ε : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, tradeSeq D ε k = D * (ε - residualSeq ε K) := by
  induction K with
  | zero => simp [residualSeq]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [tradeSeq, optTrade, residualSeq]
    ring

/-- The residual contracts to `0` as `k → ∞`. -/
theorem residualSeq_tendsto_zero (ε : ℝ) :
    Filter.Tendsto (residualSeq ε) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun k : ℕ => (2 / 3 : ℝ) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul : Filter.Tendsto (fun k : ℕ => (2 / 3 : ℝ) ^ k * ε) Filter.atTop (nhds 0) := by
    simpa using hpow.mul_const ε
  exact hmul.congr fun k => (residualSeq_closed ε k).symm

/-- Exact infinite sum of triangle trade sizes: `∑_{k ≥ 0} q_k = D * ε`. -/
theorem tradeSeq_hasSum (D ε : ℝ) :
    HasSum (tradeSeq D ε) (D * ε) := by
  have hgeom : HasSum (fun k : ℕ => (2 / 3 : ℝ) ^ k) (1 - (2 / 3 : ℝ))⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have hscaled := hgeom.mul_left (D * ε / 3)
  have hval : (D * ε / 3) * (1 - (2 / 3 : ℝ))⁻¹ = D * ε := by norm_num
  rw [hval] at hscaled
  exact hscaled.congr_fun fun k => tradeSeq_closed D ε k

/-- `tsum` form of `∑_{k ≥ 0} q_k = D * ε`. -/
theorem tradeSeq_tsum (D ε : ℝ) :
    ∑' k, tradeSeq D ε k = D * ε :=
  (tradeSeq_hasSum D ε).tsum_eq

/-- Each target contributes 3 triangle legs + 2 corrective legs per round, summing to `5 * D * ε`. -/
theorem targetPoolVolume_hasSum (D ε : ℝ) :
    HasSum (fun k => 3 * tradeSeq D ε k + 2 * tradeSeq D ε k) (5 * D * ε) := by
  have h := (tradeSeq_hasSum D ε).mul_left 5
  have hval : 5 * (D * ε) = 5 * D * ε := by ring
  rw [hval] at h
  exact h.congr_fun fun k => by ring

/-- An original/wrapper target generates 1 wrapped triangle transfer + 1 wrapped support correction
per round, summing to `2 * D * ε`. -/
theorem origWrapperTaxable_hasSum (D ε : ℝ) :
    HasSum (fun k => 1 * tradeSeq D ε k + 1 * tradeSeq D ε k) (2 * D * ε) := by
  have h := (tradeSeq_hasSum D ε).mul_left 2
  have hval : 2 * (D * ε) = 2 * D * ε := by ring
  rw [hval] at h
  exact h.congr_fun fun k => by ring

/-- A wrapper/wrapper target generates 2 wrapped triangle transfers + 2 wrapped support corrections
per round, summing to `4 * D * ε`. -/
theorem wrapperWrapperTaxable_hasSum (D ε : ℝ) :
    HasSum (fun k => 2 * tradeSeq D ε k + 2 * tradeSeq D ε k) (4 * D * ε) := by
  have h := (tradeSeq_hasSum D ε).mul_left 4
  have hval : 4 * (D * ε) = 4 * D * ε := by ring
  rw [hval] at h
  exact h.congr_fun fun k => by ring

end SingleTarget

section SmallBurn

/-- General first-order burn expansion: if proportional-burn taxable volume `T(f)` satisfies
`T(f) = T₀ + O(f)` as `f → 0`, then total burn `B(f) = f * T(f)` satisfies
`B(f) = f * T₀ + O(f^2)`. -/
theorem burn_firstOrder_isBigO {T : ℝ → ℝ} {T₀ : ℝ}
    (hT : Asymptotics.IsBigO (nhds 0) (fun f => T f - T₀) id) :
    Asymptotics.IsBigO (nhds 0) (fun f => f * T f - f * T₀) (fun f => f ^ 2) := by
  have hid : Asymptotics.IsBigO (nhds (0 : ℝ)) (id : ℝ → ℝ) id := Asymptotics.isBigO_refl _ _
  have hmul := hid.mul hT
  refine hmul.congr (fun f => ?_) (fun f => ?_)
  · simp [mul_sub]
  · simp [sq]

/-- Explicit threshold-stopped proportional-burn model on a single target:
given initial residual `ε ≥ 0`, depth `D ≥ 0`, and per-unit burn friction coefficient `c > 0`,
if rounds execute until the first index `K` where `r_K ≤ c * f`, then there exists such a
stopping round `K` for every `f > 0`, and the truncated trade sum satisfies
`0 ≤ D * ε - ∑_{k < K} q_k ≤ D * c * f`. -/
theorem exists_threshold_stopping_round {D ε c f : ℝ}
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hc : 0 < c) (hf : 0 < f) :
    ∃ K : ℕ,
      residualSeq ε K ≤ c * f ∧
      0 ≤ D * ε - ∑ k ∈ Finset.range K, tradeSeq D ε k ∧
      D * ε - ∑ k ∈ Finset.range K, tradeSeq D ε k ≤ D * c * f := by
  have hcf : 0 < c * f := mul_pos hc hf
  have htend := residualSeq_tendsto_zero ε
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨K, hK⟩ := htend (c * f) hcf
  have hdist := hK K le_rfl
  rw [Real.dist_eq, sub_zero] at hdist
  have hr_nonneg : 0 ≤ residualSeq ε K := by
    rw [residualSeq_closed]
    positivity
  have hr_le : residualSeq ε K ≤ c * f := by
    have habs : |residualSeq ε K| = residualSeq ε K := abs_of_nonneg hr_nonneg
    linarith
  refine ⟨K, hr_le, ?_, ?_⟩
  · rw [tradeSeq_partial_sum]
    have : D * ε - D * (ε - residualSeq ε K) = D * residualSeq ε K := by ring
    rw [this]
    exact mul_nonneg hD hr_nonneg
  · rw [tradeSeq_partial_sum]
    have : D * ε - D * (ε - residualSeq ε K) = D * residualSeq ε K := by ring
    rw [this]
    have hmul : D * residualSeq ε K ≤ D * (c * f) := mul_le_mul_of_nonneg_left hr_le hD
    linarith

/-- Quantitative `O(f^2)` burn-remainder theorem for any schedule whose realized taxable volume
under proportional burn `f ≥ 0` stays within `C * f` of the zero-burn baseline `T₀`. -/
theorem burn_quantitative_sq_bound {T : ℝ → ℝ} {T₀ C : ℝ}
    (hbound : ∀ f ≥ 0, |T f - T₀| ≤ C * f) :
    (∀ f ≥ 0, |f * T f - f * T₀| ≤ C * f ^ 2) ∧
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun f => f * T f - f * T₀) (fun f => f ^ 2) := by
  have hpt : ∀ f ≥ 0, |f * T f - f * T₀| ≤ C * f ^ 2 := by
    intro f hf
    have hfac : f * T f - f * T₀ = f * (T f - T₀) := by ring
    rw [hfac, abs_mul, abs_of_nonneg hf]
    calc f * |T f - T₀| ≤ f * (C * f) := mul_le_mul_of_nonneg_left (hbound f hf) hf
      _ = C * f ^ 2 := by ring
  refine ⟨hpt, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨|C|, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with f hf
  have hf0 : 0 ≤ f := hf
  have h1 := hpt f hf0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg f)]
  calc |f * T f - f * T₀| ≤ C * f ^ 2 := h1
    _ ≤ |C| * f ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg f)

end SmallBurn

end Cascades
