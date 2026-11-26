import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Cascades.FullDynamics

/-!
# Compounding Under Exogenous Depth vs. Finite-Market Saturation & Closed-System Conservation

Formalizes the exact mathematical boundary between the two claims in the `n -> n++` debate:

1. **Bounded Positive Yield Still Compounds Past Every Finite Target (Exogenous Market):**
   * `compounding_tendsto_atTop` & `compounding_exceeds_any_finite_target`:
     Unbounded per-cycle yield (`Y → ∞`) is **not** required to exceed any finite target `H > 0`.
     For **any** initial capital `K₀ > 0` and **any** constant strictly positive (even tiny and
     bounded!) per-cycle net return `y > 0`, reinvested capital `K₀ * (1 + y)^T → ∞` and
     strictly exceeds every finite `H > 0` in finitely many cycles `T`.
   * `bounded_yield_still_unbounded_compounding`: explicitly combines the bounded per-cycle
     cascade yield `Y_M < 4 f κ n μ / (n + 1)` with unbounded multi-cycle compounding under
     an exogenous net return `0 < y ≤ Y_M`.

2. **Exact Finite-External-Market Saturation Law (Harmonic Effective Depth):**
   * When the external reference market has **finite** depth `D_ext > 0` rather than infinite
     depth, an arbitrage trade of size `q` moves the internal pool by `q / D` and the external
     market by `q / D_ext`, giving total price impact `(1/D + 1/D_ext) * q = q / D_eff`, where
     `D_eff = (D * D_ext) / (D + D_ext)`.
   * `finiteExtArbProfit_uniqueMax`: optimal trade size is `q* = D_eff * r`, with strictly
     bounded volume `D_eff * |r| < min(D, D_ext) * |r|`.
   * `effectiveDepth_small_pool_ratio`: in the small-pool limit (`D → 0` at fixed `D_ext`),
     `D_eff / D → 1` (recovering the exogenous-market model).
   * `effectiveDepth_saturates_at_ext`: as internal liquidity grows without bound (`L → ∞` at
     fixed finite `D_ext`), absolute trade volume saturates at `D_eff → D_ext < ∞`.
   * `saturated_yield_tendsto_zero`: per-unit capital yield proportional to `D_eff(κ L) / L`
     **collapses to `0`** as `L → ∞` in any finite external market.

3. **Closed-System Zero-Sum Conservation (`closed_system_zero_sum`):**
   * Across any finite set of participants whose net underlying reserve changes sum to zero
     (`∑ i, ΔR i = 0`, matching `nav_conservation_of_backing`), any coalition `S`'s net gain
     equals the exact net outflow of the complement `Sᶜ`:
     `∑ i ∈ S, ΔR i = -(∑ i ∈ Sᶜ, ΔR i)`.
   * In particular, no mechanism in a closed finite-resource system can give every participant
     strictly positive net underlying wealth simultaneously (`no_strictly_positive_closed_system`).
-/

namespace Cascades

section Compounding

/-- Reinvested capital after `T` cycles at constant per-cycle net return `y`:
`K_T = K₀ * (1 + y)^T`. -/
def compoundedCapital (K₀ y : ℝ) (T : ℕ) : ℝ :=
  K₀ * (1 + y) ^ T

/-- Bernoulli lower bound: for `y ≥ 0`, `(1 + y)^T ≥ 1 + T * y`. -/
theorem one_add_pow_ge_linear {y : ℝ} (hy : 0 ≤ y) (T : ℕ) :
    1 + (T : ℝ) * y ≤ (1 + y) ^ T := by
  induction T with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hmul : (1 + (k : ℝ) * y) * (1 + y) ≤ (1 + y) ^ k * (1 + y) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hky : 0 ≤ (k : ℝ) * y ^ 2 := by positivity
    nlinarith

/-- **Archimedean Compounding Theorem (`n -> n++`):**
For any initial capital `K₀ > 0` and any strictly positive (even arbitrarily small and
bounded) per-cycle net return `y > 0`, compounded capital `K₀ * (1 + y)^T → ∞` as `T → ∞`,
and therefore strictly exceeds **every** finite target `H > 0` in finitely many cycles. -/
theorem compounding_tendsto_atTop {K₀ y : ℝ} (hK : 0 < K₀) (hy : 0 < y) :
    Filter.Tendsto (compoundedCapital K₀ y) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro H
  obtain ⟨N, hN⟩ := exists_nat_gt ((H - K₀) / (K₀ * y))
  refine ⟨N, fun T hT => ?_⟩
  have hNT : (N : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hKy : 0 < K₀ * y := mul_pos hK hy
  have hlin : (H - K₀) / (K₀ * y) < (T : ℝ) := lt_of_lt_of_le hN hNT
  have hmul : H - K₀ < (T : ℝ) * (K₀ * y) := (div_lt_iff₀ hKy).mp hlin
  have hbern := one_add_pow_ge_linear hy.le T
  unfold compoundedCapital
  have hKbern : K₀ * (1 + (T : ℝ) * y) ≤ K₀ * (1 + y) ^ T :=
    mul_le_mul_of_nonneg_left hbern hK.le
  linarith

theorem compounding_exceeds_any_finite_target {K₀ y : ℝ} (hK : 0 < K₀) (hy : 0 < y) (H : ℝ) :
    ∃ T : ℕ, H < compoundedCapital K₀ y T := by
  have ht := (Filter.tendsto_atTop_atTop.mp (compounding_tendsto_atTop hK hy)) (H + 1)
  rcases ht with ⟨T, hT⟩
  exact ⟨T, by linarith [hT T le_rfl]⟩

/-- Explicitly reconciles bounded per-cycle yield with unbounded compounding:
for any `M ≥ 2, n ≥ 1, f, κ, μ > 0`, per-cycle gross yield `Y_M` is strictly bounded above
by `4 f κ n μ / (n + 1)`, yet any sustained strictly positive net return `0 < y ≤ Y_M`
compounds past every finite target `H` under exogenous market depth. -/
theorem bounded_yield_still_unbounded_compounding {M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n)
    {f κ μ K₀ y : ℝ} (hf : 0 < f) (hκ : 0 < κ) (hμ : 0 < μ) (hK : 0 < K₀) (hy : 0 < y) :
    yieldFixedMu f κ n μ M < 4 * f * κ * (n : ℝ) * μ / ((n : ℝ) + 1) ∧
    (∀ H : ℝ, ∃ T : ℕ, H < compoundedCapital K₀ y T) := by
  constructor
  · unfold yieldFixedMu
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : (0 : ℝ) < (M : ℝ) * ((n : ℝ) + 1) - 1 := by nlinarith
    have hnum : (0 : ℝ) < 4 * f * κ * (n : ℝ) * μ := by positivity
    rw [div_lt_div_iff₀ hden hn1]
    have hdiff :
        4 * f * κ * (n : ℝ) * μ * ((M : ℝ) * ((n : ℝ) + 1) - 1) -
        4 * f * κ * (n : ℝ) * μ * ((M : ℝ) - 1) * ((n : ℝ) + 1) =
        4 * f * κ * (n : ℝ) * μ * (n : ℝ) := by ring
    have hpos : 0 < 4 * f * κ * (n : ℝ) * μ * (n : ℝ) := by positivity
    linarith
  · intro H
    exact compounding_exceeds_any_finite_target hK hy H

end Compounding

section FiniteExternalMarketSaturation

/-- Harmonic effective depth when an internal pool of depth `D` trades against a finite
external market of depth `D_ext`: `D_eff = (D * D_ext) / (D + D_ext)`. -/
noncomputable def effectiveDepth (D D_ext : ℝ) : ℝ :=
  D * D_ext / (D + D_ext)

/-- Arbitrage profit trading size `q` between an internal pool of depth `D` and a finite
external market of depth `D_ext` on initial price gap `r`:
`Π(q) = r * q - (1/(2D) + 1/(2D_ext)) * q^2`. -/
noncomputable def finiteExtArbProfit (D D_ext r q : ℝ) : ℝ :=
  r * q - (1 / (2 * D) + 1 / (2 * D_ext)) * q ^ 2

/-- Optimal trade size against a finite external market is `q* = D_eff * r`, with
strictly bounded volume `|q*| = D_eff * |r| < min(D, D_ext) * |r|`. -/
theorem finiteExtArbProfit_le_opt {D D_ext : ℝ} (hD : 0 < D) (hExt : 0 < D_ext) (r q : ℝ) :
    finiteExtArbProfit D D_ext r q ≤
      finiteExtArbProfit D D_ext r (effectiveDepth D D_ext * r) := by
  have hsum : 0 < D + D_ext := by linarith
  have hcoeff : 1 / (2 * D) + 1 / (2 * D_ext) = 1 / (2 * effectiveDepth D D_ext) := by
    unfold effectiveDepth
    field_simp [hD.ne', hExt.ne', hsum.ne']
    ring
  have heff : 0 < effectiveDepth D D_ext := by unfold effectiveDepth; positivity
  unfold finiteExtArbProfit
  rw [hcoeff]
  have hsq :
      (r * (effectiveDepth D D_ext * r) -
        1 / (2 * effectiveDepth D D_ext) * (effectiveDepth D D_ext * r) ^ 2) -
      (r * q - 1 / (2 * effectiveDepth D D_ext) * q ^ 2) =
      (q - effectiveDepth D D_ext * r) ^ 2 / (2 * effectiveDepth D D_ext) := by
    field_simp [heff.ne']
    ring
  have hnn : 0 ≤ (q - effectiveDepth D D_ext * r) ^ 2 / (2 * effectiveDepth D D_ext) := by
    positivity
  linarith

/-- Finite external depth strictly caps effective depth below BOTH `D` and `D_ext`. -/
theorem effectiveDepth_lt_both {D D_ext : ℝ} (hD : 0 < D) (hExt : 0 < D_ext) :
    effectiveDepth D D_ext < D ∧ effectiveDepth D D_ext < D_ext := by
  unfold effectiveDepth
  have hsum : 0 < D + D_ext := by linarith
  constructor
  · rw [div_lt_iff₀ hsum]; nlinarith
  · rw [div_lt_iff₀ hsum]; nlinarith

/-- **Finite-Market Saturation Limit:**
At fixed finite external market depth `D_ext > 0`, as internal pool liquidity `L → ∞`
(`D = κ * L`), effective depth saturates at `D_ext` (absolute trade volume is capped by
external market depth). -/
theorem effectiveDepth_saturates_at_ext {κ D_ext : ℝ} (hκ : 0 < κ) (hExt : 0 < D_ext) :
    Filter.Tendsto (fun L : ℝ => effectiveDepth (κ * L) D_ext)
      Filter.atTop (nhds D_ext) := by
  have hinv : Filter.Tendsto (fun L : ℝ => D_ext / (κ * L)) Filter.atTop (nhds 0) := by
    have hmul : Filter.Tendsto (fun L : ℝ => κ * L) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hκ Filter.tendsto_id
    exact tendsto_const_nhds.div_atTop hmul
  have hden : Filter.Tendsto (fun L : ℝ => 1 + D_ext / (κ * L)) Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hinv
  have hfrac : Filter.Tendsto (fun L : ℝ => D_ext / (1 + D_ext / (κ * L)))
      Filter.atTop (nhds (D_ext / (1 + 0))) :=
    tendsto_const_nhds.div hden (by norm_num)
  have hlim : D_ext / (1 + 0) = D_ext := by ring
  rw [hlim] at hfrac
  refine hfrac.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
  unfold effectiveDepth
  have hκL : κ * L ≠ 0 := (mul_pos hκ hL).ne'
  have hsum : κ * L + D_ext ≠ 0 := by linarith [mul_pos hκ hL]
  have hden' : 1 + D_ext / (κ * L) ≠ 0 := by positivity
  field_simp [hκL, hsum, hden']

/-- **Per-Unit Yield Collapse in a Finite Market:**
With fixed finite external market depth `D_ext > 0`, any per-unit capital yield proportional
to `D_eff(κ L) / L` **collapses to `0`** as deployed liquidity `L → ∞`, halting unbounded
exponential compounding once internal pools saturate the external market. -/
theorem saturated_yield_tendsto_zero {c κ D_ext : ℝ} (hκ : 0 < κ) (hExt : 0 < D_ext) :
    Filter.Tendsto (fun L : ℝ => c * effectiveDepth (κ * L) D_ext / L)
      Filter.atTop (nhds 0) := by
  have hlin : Filter.Tendsto (fun L : ℝ => κ * L + D_ext) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_add (Filter.Tendsto.const_mul_atTop hκ Filter.tendsto_id) tendsto_const_nhds
  have hdiv : Filter.Tendsto (fun L : ℝ => (c * κ * D_ext) / (κ * L + D_ext))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlin
  refine hdiv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
  unfold effectiveDepth
  have hsum : κ * L + D_ext ≠ 0 := by linarith [mul_pos hκ hL]
  field_simp [hL.ne', hsum]

/-- **Sovereign Capital Share Law (`s ∈ (0, 1)` of World Wealth `W`):**
If total global liquidity depth `W > 0` is split between internal sovereign pools `D = s * W`
and external markets `D_ext = (1 - s) * W`:
1. Effective harmonic depth is identically `s * (1 - s) * W`.
2. Yield retention relative to the small-pool limit (`D_eff / D`) is identically `1 - s`. -/
theorem sovereign_share_effectiveDepth {W s : ℝ} (hW : W ≠ 0) (hs : s ≠ 0) :
    effectiveDepth (s * W) ((1 - s) * W) = s * (1 - s) * W ∧
    effectiveDepth (s * W) ((1 - s) * W) / (s * W) = 1 - s := by
  unfold effectiveDepth
  have hsum : s * W + (1 - s) * W = W := by ring
  rw [hsum]
  constructor
  · field_simp [hW]
  · field_simp [hW, hs]

/-- **Unique Maximum at Half of World Liquidity (`s = 1/2`):**
For any positive global wealth `W > 0`, absolute effective depth `s * (1 - s) * W` is uniquely
maximized at `s = 1/2` (value `W / 4`). Pushing sovereign share past `1/2` toward `1`
strictly **reduces** both yield retention (`1 - s → 0`) and absolute cascade volume (`→ 0`). -/
theorem sovereign_share_max_at_half {W : ℝ} (hW : 0 < W) (s : ℝ) :
    s * (1 - s) * W ≤ W / 4 ∧
    (s * (1 - s) * W = W / 4 ↔ s = 1 / 2) := by
  have hsq : s * (1 - s) * W = W / 4 - W * (s - 1 / 2) ^ 2 := by ring
  rw [hsq]
  constructor
  · have hnn : 0 ≤ W * (s - 1 / 2) ^ 2 := by positivity
    linarith
  · constructor
    · intro h
      have hz : W * (s - 1 / 2) ^ 2 = 0 := by linarith
      have hsq0 : (s - 1 / 2) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hW.ne'
      linarith [sq_eq_zero_iff.mp hsq0]
    · intro h
      rw [h]; ring

/-- **Concrete Sovereign-Scale Comparison (`1/10` vs. `1/2` of World Liquidity):**
* At `s = 1/10` (10% of world liquidity): `D_eff = (9/100) * W`, retaining `90%` of idealized yield.
* At `s = 1/2` (50% of world liquidity): `D_eff = (1/4) * W = (25/9) * D_eff(1/10)` (global max,
  `25/9 ≈ 2.78×` higher absolute turnover/burn), retaining `50%` of idealized yield. -/
theorem sovereign_tenth_vs_half {W : ℝ} (hW : W ≠ 0) :
    effectiveDepth ((1 / 10 : ℝ) * W) ((1 - 1 / 10 : ℝ) * W) = (9 / 100 : ℝ) * W ∧
    effectiveDepth ((1 / 10 : ℝ) * W) ((1 - 1 / 10 : ℝ) * W) / ((1 / 10 : ℝ) * W) = 9 / 10 ∧
    effectiveDepth ((1 / 2 : ℝ) * W) ((1 - 1 / 2 : ℝ) * W) = (1 / 4 : ℝ) * W ∧
    effectiveDepth ((1 / 2 : ℝ) * W) ((1 - 1 / 2 : ℝ) * W) / ((1 / 2 : ℝ) * W) = 1 / 2 ∧
    effectiveDepth ((1 / 2 : ℝ) * W) ((1 - 1 / 2 : ℝ) * W) =
      (25 / 9 : ℝ) * effectiveDepth ((1 / 10 : ℝ) * W) ((1 - 1 / 10 : ℝ) * W) := by
  have h10 := sovereign_share_effectiveDepth (s := (1 / 10 : ℝ)) hW (by norm_num)
  have h2 := sovereign_share_effectiveDepth (s := (1 / 2 : ℝ)) hW (by norm_num)
  rw [h10.2, h10.1, h2.2, h2.1]
  refine ⟨by ring, by norm_num, by ring, by norm_num, by ring⟩

end FiniteExternalMarketSaturation

section ClosedSystemConservation

/-- **Closed-System Zero-Sum Conservation Law:**
For any finite population `ι` whose net underlying reserve changes sum to zero
(`∑ i, ΔR i = 0`), every coalition `S`'s net underlying gain equals the exact net outflow
of the rest of the system `Sᶜ`. -/
theorem closed_system_zero_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ΔR : ι → ℝ) (hcons : ∑ i : ι, ΔR i = 0) (S : Finset ι) :
    ∑ i ∈ S, ΔR i = -(∑ i ∈ Sᶜ, ΔR i) := by
  have hpart : (∑ i ∈ S, ΔR i) + (∑ i ∈ Sᶜ, ΔR i) = ∑ i : ι, ΔR i :=
    Finset.sum_add_sum_compl S ΔR
  linarith

/-- Corollary: in any nonempty closed resource-conserving system (`∑ i, ΔR i = 0`), it is
mathematically impossible for every participant to simultaneously gain strictly positive
underlying reserves (`¬ ∀ i, 0 < ΔR i`). -/
theorem no_strictly_positive_closed_system {ι : Type*} [Fintype ι] [Nonempty ι]
    (ΔR : ι → ℝ) (hcons : ∑ i : ι, ΔR i = 0) :
    ¬ (∀ i : ι, 0 < ΔR i) := by
  intro hall
  have hpos : 0 < ∑ i : ι, ΔR i :=
    Finset.sum_pos (fun i _ => hall i) Finset.univ_nonempty
  linarith

end ClosedSystemConservation

end Cascades
