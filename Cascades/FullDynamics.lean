import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Cascades.NetLedger

/-!
# Full Dynamics: Exact Burn/NAV Feedback, Non-Exempt Taxes, Backing Costs & Multi-Period Regimes

Formalizes the four remaining structural extensions flagged in `cascades.md` and the README:

1. **Exact Nonlinear Burn-Supply-NAV Feedback (beyond `O(f^2)`):**
   * `nav_appreciation_exact`: burning fraction `b = B_sh / S₀ ∈ [0, 1)` of wrapper supply with
     intact backing reserve `R₀` increases per-share NAV by exact factor `1 / (1 - b)`, i.e.
     relative NAV appreciation `b / (1 - b) = b + b^2 / (1 - b)`.
   * `nav_appreciation_gt_linear` & `nav_exact_remainder_bounds`: nonlinear feedback strictly
     exceeds the first-order term `b` and satisfies exact bounds `b^2 ≤ b/(1-b) - b ≤ 2 b^2`
     for `0 ≤ b ≤ 1/2`.
   * `nav_conservation_of_backing`: `(S₀ - B_sh) * NAV(B_sh) = R₀` identically (burning shares
     redistributes backing claims without creating new external assets).
   * `nav_feedback_geometric_hasSum`: exact all-orders convergent secondary spoke-arbitrage
     feedback series `∑_{k≥0} b * ρ^k = b / (1 - ρ)` whenever feedback contraction `0 ≤ ρ < 1`.

2. **Non-Exempt Mint/Redemption & Router-Intermediary Taxes:**
   * Parameterized transfer burn `f ≥ 0`, non-exempt mint/redemption tax `τ_m ≥ 0`, and `k_r : ℕ`
     extra router-intermediary hops per wrapped leg.
   * `generalized_cascade_ratio` & `generalized_ratio_bounds`: exact cascade-to-direct burn/tax
     ratio `(2(1+k_r)f + τ_m) / ((1+k_r)f + τ_m) = 1 + (1+k_r)f / ((1+k_r)f + τ_m)` — recovering
     `2×` when `τ_m = 0`, `1.5×` when `τ_m = f, k_r = 0`, and strictly in `(1, 2)` for `f, τ_m > 0`.
   * `tax_choke_threshold`: exact per-target residual activation hurdle below which non-exempt
     mint/redemption and router taxes choke off profitable execution.

3. **Separately Funded Backing Reserves & Borrow/Carry Costs:**
   * `consolidated_yield_dilution` & `consolidated_yield_tendsto`: proportional backing
     `K_back = λ_b K_pool` dilutes gross yield by exact factor `1 / (1 + λ_b)` while preserving
     strict monotonicity in `M` and limit `4 f κ n μ / ((1 + λ_b)(n + 1))`.
   * `linear_backing_dilution_vanishes`: if backing scales only linearly in wrapper count `O(M)`
     while pool capital scales quadratically `O(M^2)`, backing dilution ratio `K_back / K_pool → 0`.
   * `consolidated_net_roi_pos_iff`: exact necessary and sufficient condition for positive
     consolidated net ROI after both LVR and carry/borrow cost `r_c ≥ 0`.

4. **Multi-Period Price Regimes (Mean-Reverting vs. Symmetric Random Walk vs. Trending):**
   * `multiperiod_lvr_regime_invariant`: against continuous dynamic rebalancing (LVR benchmark),
     `T`-step net P&L equals `T *` single-step net P&L regardless of path direction.
   * `meanReverting_beats_hodl_eventually`: on any bounded mean-reverting path (`|u_T - u₀| ≤ B`),
     linear cumulative revenue `Θ(T)` strictly beats `O(1)` terminal IL vs. HODL for all
     `T > m^2 B^2 / (2 c_rev ε)`.
   * `trending_loses_to_hodl_eventually`: on a monotone trending path (`|u_T - u₀| = T ε`),
     quadratic terminal IL `Θ(T^2)` strictly overwhelms linear revenue `Θ(T)` for all
     `T > 2 c_rev / (m^2 ε)`.
   * `randomWalk_expected_sq_displacement` & `randomWalk_expected_netPnL_pos_iff`: exact finite
     expectation over all `2^T` symmetric binary paths proves `E[(u_T - u₀)^2] = T ε^2`, so
     expected net P&L vs. HODL equals `T`-step net P&L vs. LVR and is positive iff `ε < 2 c_rev / m^2`.
-/

namespace Cascades

section ExactNAVFeedback

/-- Exact per-share NAV of a transfer-burn wrapper with backing reserve `R₀`, initial supply
`S₀`, and cumulative burned supply `B_sh`: `NAV = R₀ / (S₀ - B_sh)`. -/
noncomputable def wrapperNAV (R₀ S₀ B_sh : ℝ) : ℝ :=
  R₀ / (S₀ - B_sh)

/-- Exact zero-asset-creation conservation identity: total backing claim of all remaining shares
equals the original reserve `R₀` identically (burns redistribute claims, not external assets). -/
theorem nav_conservation_of_backing {R₀ S₀ B_sh : ℝ} (hS : S₀ - B_sh ≠ 0) :
    (S₀ - B_sh) * wrapperNAV R₀ S₀ B_sh = R₀ := by
  unfold wrapperNAV
  exact mul_div_cancel₀ R₀ hS

/-- Exact all-orders relative NAV appreciation as a function of burned supply fraction
`b = B_sh / S₀`: `(NAV(b S₀) - NAV(0)) / NAV(0) = b / (1 - b) = b + b^2 / (1 - b)`. -/
theorem nav_appreciation_exact {R₀ S₀ b : ℝ} (hR : R₀ ≠ 0) (hS : S₀ ≠ 0) (hb : b ≠ 1) :
    (wrapperNAV R₀ S₀ (b * S₀) - wrapperNAV R₀ S₀ 0) / wrapperNAV R₀ S₀ 0 = b / (1 - b) ∧
    b / (1 - b) = b + b ^ 2 / (1 - b) := by
  have h1b : 1 - b ≠ 0 := sub_ne_zero.mpr hb.symm
  have hsub : S₀ - b * S₀ ≠ 0 := by
    have : S₀ - b * S₀ = (1 - b) * S₀ := by ring
    rw [this]; exact mul_ne_zero h1b hS
  constructor
  · unfold wrapperNAV
    field_simp [hR, hS, h1b, hsub]
    ring
  · field_simp [h1b]
    ring

/-- Strict super-linearity of exact burn-NAV feedback: for all `0 < b < 1`, exact NAV
appreciation `b / (1 - b)` strictly exceeds its first-order linear approximation `b`. -/
theorem nav_appreciation_gt_linear {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    b < b / (1 - b) := by
  have h1b : 0 < 1 - b := by linarith
  have hrem : 0 < b ^ 2 / (1 - b) := by positivity
  have heq : b / (1 - b) = b + b ^ 2 / (1 - b) := by
    field_simp [h1b.ne']; ring
  linarith

/-- Explicit two-sided non-asymptotic remainder bounds beyond `O(f^2)`:
for all `0 ≤ b ≤ 1/2`, `b^2 ≤ b / (1 - b) - b ≤ 2 * b^2`. -/
theorem nav_exact_remainder_bounds {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) :
    b ^ 2 ≤ b / (1 - b) - b ∧ b / (1 - b) - b ≤ 2 * b ^ 2 := by
  have h1b : 0 < 1 - b := by linarith
  have heq : b / (1 - b) - b = b ^ 2 / (1 - b) := by
    field_simp [h1b.ne']; ring
  rw [heq]
  constructor
  · rw [le_div_iff₀ h1b]
    nlinarith [sq_nonneg b]
  · rw [div_le_iff₀ h1b]
    nlinarith [sq_nonneg b]

/-- Exact all-orders secondary spoke-arbitrage NAV-feedback series:
if each wave of secondary NAV-drift arbitrage triggers a contraction fraction `0 ≤ ρ < 1`
of additional burn, total all-orders burned fraction converges to `b / (1 - ρ)`. -/
theorem nav_feedback_geometric_hasSum {b ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HasSum (fun k : ℕ => b * ρ ^ k) (b / (1 - ρ)) := by
  have hgeom := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left b
  simpa [div_eq_mul_inv] using hgeom

end ExactNAVFeedback

section NonExemptTaxesAndRouters

/-- Per-unit tax paid on direct external correction of a target with `w` wrapped endpoints,
transfer burn rate `f`, non-exempt mint/redemption tax `τ_m`, and `k_r` extra router hops. -/
def directUnitTax (w : ℕ) (f τm : ℝ) (kr : ℕ) : ℝ :=
  (w : ℝ) * (((kr : ℝ) + 1) * f + τm)

/-- Per-unit tax generated by one cascade target (pool-to-pool triangle + two external support
corrections) with `w` wrapped target endpoints and original pivot. -/
def cascadeUnitTax (w : ℕ) (f τm : ℝ) (kr : ℕ) : ℝ :=
  (w : ℝ) * (2 * ((kr : ℝ) + 1) * f + τm)

/-- **Exact Generalized Cascade-to-Direct Tax Ratio:**
With transfer burn `f`, non-exempt mint/redemption tax `τ_m`, and `k_r` router hops,
the cascade-to-direct ratio equals `(2(k_r + 1)f + τ_m) / ((k_r + 1)f + τ_m)`
`= 1 + (k_r + 1)f / ((k_r + 1)f + τ_m)`:
* Equals `2` identically when mint/redemption is exempt (`τ_m = 0`), for any `k_r`.
* Equals `3 / 2` when mint/redemption is equally taxed (`τ_m = f, k_r = 0`).
* Lies strictly in `(1, 2)` whenever both `f > 0` and `τ_m > 0`. -/
theorem generalized_cascade_ratio {w kr : ℕ} (hw : 0 < w) {f τm : ℝ}
    (hden : ((kr : ℝ) + 1) * f + τm ≠ 0) :
    cascadeUnitTax w f τm kr / directUnitTax w f τm kr =
      1 + ((kr : ℝ) + 1) * f / (((kr : ℝ) + 1) * f + τm) := by
  unfold cascadeUnitTax directUnitTax
  have hw' : (w : ℝ) ≠ 0 := by positivity
  field_simp [hw', hden]
  ring

theorem generalized_ratio_special_cases {w kr : ℕ} (hw : 0 < w) {f τm : ℝ}
    (hf : 0 < f) (hτ : 0 < τm) :
    cascadeUnitTax w f 0 kr / directUnitTax w f 0 kr = 2 ∧
    cascadeUnitTax w f f 0 / directUnitTax w f f 0 = 3 / 2 ∧
    1 < cascadeUnitTax w f τm kr / directUnitTax w f τm kr ∧
    cascadeUnitTax w f τm kr / directUnitTax w f τm kr < 2 := by
  have hk : (0 : ℝ) < (kr : ℝ) + 1 := by positivity
  have hkf : 0 < ((kr : ℝ) + 1) * f := mul_pos hk hf
  have hden0 : ((kr : ℝ) + 1) * f + 0 ≠ 0 := by linarith
  have hdenf : (((0 : ℕ) : ℝ) + 1) * f + f ≠ 0 := by simp; linarith
  have hdenτ : ((kr : ℝ) + 1) * f + τm ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [generalized_cascade_ratio hw hden0]
    field_simp [hkf.ne']
    ring
  · rw [generalized_cascade_ratio hw hdenf]
    field_simp [hf.ne']
    ring
  · rw [generalized_cascade_ratio hw hdenτ]
    have hpos : 0 < ((kr : ℝ) + 1) * f / (((kr : ℝ) + 1) * f + τm) := by positivity
    linarith
  · rw [generalized_cascade_ratio hw hdenτ]
    have hlt : ((kr : ℝ) + 1) * f / (((kr : ℝ) + 1) * f + τm) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith

/-- **Exact Non-Exempt Tax Activation Hurdle:**
With per-unit triangle tax `c_tri = w * (k_r + 1) * f` and per-unit support restoration tax
`c_sup = (k_r + 1) * f + τ_m`:
1. The net triangular profit `(r - c_tri) q - 3 q^2 / (2 D)` has a strictly positive trade
   iff `r > c_tri`.
2. External restoration of a displaced wrapped support (residual `r / 3`) is strictly
   profitable iff `r > 3 * c_sup`. -/
theorem tax_choke_threshold {D r : ℝ} (hD : 0 < D) (w kr : ℕ) (f τm : ℝ) :
    let c_tri := (w : ℝ) * ((kr : ℝ) + 1) * f
    let c_sup := ((kr : ℝ) + 1) * f + τm
    ((∃ q > 0, (r - c_tri) * q - 3 * q ^ 2 / (2 * D) > 0) ↔ c_tri < r) ∧
    (0 < r / 3 - c_sup ↔ 3 * c_sup < r) := by
  intro c_tri c_sup
  constructor
  · constructor
    · rintro ⟨q, hq, hprof⟩
      have hsq : 0 < 3 * q ^ 2 / (2 * D) := by positivity
      have hmul : 0 < (r - c_tri) * q := by linarith
      have hpos : 0 < r - c_tri := (mul_pos_iff_of_pos_right hq).mp hmul
      linarith
    · intro hr
      refine ⟨D * (r - c_tri) / 3, by positivity, ?_⟩
      have hval :
          (r - c_tri) * (D * (r - c_tri) / 3) - 3 * (D * (r - c_tri) / 3) ^ 2 / (2 * D) =
          D * (r - c_tri) ^ 2 / 6 := by
        field_simp [hD.ne']
        ring
      rw [hval]
      have hsub : 0 < r - c_tri := by linarith
      positivity
  · constructor <;> intro h <;> linarith

end NonExemptTaxesAndRouters

section BackingReservesAndCarry

/-- Consolidated capital base including separately funded backing reserves:
`K_tot = K_pool + K_back`. -/
def consolidatedCapital (K_pool K_back : ℝ) : ℝ :=
  K_pool + K_back

/-- Proportional backing (`K_back = λ_b * K_pool`, `λ_b ≥ 0`) dilutes leading gross burn yield
by the exact factor `1 / (1 + λ_b)`, preserving strict monotonicity in `M` and converging to
`4 f κ n μ / ((1 + λ_b) (n + 1))`. -/
theorem consolidated_yield_proportional_backing {M n : ℕ} (hM : 2 ≤ M)
    {f κ L μ lam_b : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam_b) :
    let K_pool := poolCapital L M n
    let K_tot := consolidatedCapital K_pool (lam_b * K_pool)
    let B₁ := leadingBurn f κ L n ((M : ℝ) * ((M : ℝ) - 1) / 2 * μ)
    B₁ / K_tot = yieldFixedMu f κ n μ M / (1 + lam_b) := by
  intro K_pool K_tot B₁
  have h1lam : 1 + lam_b ≠ 0 := by linarith
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hden : (M : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 := by
    have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hKtot : K_tot = (1 + lam_b) * K_pool := by
    dsimp [K_tot, consolidatedCapital]; ring
  rw [hKtot]
  dsimp [B₁, K_pool]
  unfold leadingBurn poolCapital poolCountReal yieldFixedMu
  field_simp [hL.ne', h1lam, hM0, hM1, hn1, hden]

/-- If backing reserves scale only linearly in total wrapper count `K_back(M) = M * n * L_b`
while complete-graph pool capital scales quadratically `K_pool(M) = L * P(M, n)`, then
backing dilution `K_back(M) / K_pool(M) → 0` as `M → ∞`. -/
theorem linear_backing_dilution_vanishes {L Lb : ℝ} (hL : 0 < L) (n : ℕ) :
    Filter.Tendsto
      (fun M : ℕ => ((M : ℝ) * (n : ℝ) * Lb) / poolCapital L M n)
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun M : ℕ => (1 : ℝ) / (M : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hden : Filter.Tendsto (fun M : ℕ => ((n : ℝ) + 1) - (1 : ℝ) / (M : ℝ))
      Filter.atTop (nhds (((n : ℝ) + 1) - 0)) :=
    tendsto_const_nhds.sub hinv
  have hne : ((n : ℝ) + 1) - 0 ≠ 0 := by rw [sub_zero]; positivity
  have hfrac : Filter.Tendsto
      (fun M : ℕ => ((1 : ℝ) / (M : ℝ)) / (((n : ℝ) + 1) - (1 : ℝ) / (M : ℝ)))
      Filter.atTop (nhds (0 / (((n : ℝ) + 1) - 0))) :=
    hinv.div hden hne
  have hscaled := hfrac.const_mul (2 * (n : ℝ) * Lb / (L * ((n : ℝ) + 1)))
  have hlim : 2 * (n : ℝ) * Lb / (L * ((n : ℝ) + 1)) * (0 / (((n : ℝ) + 1) - 0)) = 0 := by ring
  rw [hlim] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with M hM
  unfold poolCapital poolCountReal
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (M : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 := by nlinarith
  have hd' : ((n : ℝ) + 1) - 1 / (M : ℝ) ≠ 0 := by
    intro h
    have : (M : ℝ) * (((n : ℝ) + 1) - 1 / (M : ℝ)) = 0 := by rw [h, mul_zero]
    have h2 : (M : ℝ) * (((n : ℝ) + 1) - 1 / (M : ℝ)) = (M : ℝ) * ((n : ℝ) + 1) - 1 := by
      field_simp [hM0]
    exact hd (h2.symm.trans this)
  field_simp [hL.ne', hM0, hn1, hd, hd']

/-- **Consolidated Net ROI Break-Even Including Backing Reserves & Carry/Borrow Cost `r_c`:**
For total consolidated capital `K_tot = K_pool + K_back > 0`, gross burn `B`, LP fees `F`,
LVR cost `LVR`, and carry/funding rate `r_c`, consolidated net profit `B + F - LVR - r_c K_tot`
is strictly positive iff total gross yield `(B + F) / K_tot` exceeds `LVR / K_tot + r_c`. -/
theorem consolidated_net_roi_pos_iff {K_tot B F LVR r_c : ℝ} (hK : 0 < K_tot) :
    0 < B + F - LVR - r_c * K_tot ↔ LVR / K_tot + r_c < (B + F) / K_tot := by
  have h1 : (B + F - LVR - r_c * K_tot) / K_tot = (B + F) / K_tot - (LVR / K_tot + r_c) := by
    field_simp [hK.ne']
    ring
  constructor
  · intro h
    have hpos : 0 < (B + F - LVR - r_c * K_tot) / K_tot := div_pos h hK
    linarith
  · intro h
    have hpos : 0 < (B + F - LVR - r_c * K_tot) / K_tot := by linarith
    exact (div_pos_iff_of_pos_right hK).mp hpos

end BackingReservesAndCarry

section MultiPeriodPriceRegimes

/-- **Regime-Invariance Against Dynamic Rebalancing (LVR Benchmark):**
Across `T ≥ 1` discrete steps each of magnitude `ε > 0`, cumulative burn + fee revenue
`T * c_rev * D * ε` minus cumulative dynamic-rebalancing LVR `T * (D / 2) * m^2 * ε^2`
is strictly positive iff `ε < 2 * c_rev / m^2` — completely independent of `T` and whether
the path mean-reverts or trends. -/
theorem multiperiod_lvr_regime_invariant {T : ℕ} (hT : 1 ≤ T)
    {D c_rev m ε : ℝ} (hD : 0 < D) (hm : 0 < m) (hε : 0 < ε) :
    0 < (T : ℝ) * (c_rev * D * ε) - (T : ℝ) * (D / 2 * m ^ 2 * ε ^ 2) ↔
      ε < 2 * c_rev / m ^ 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hm2 : 0 < m ^ 2 := by positivity
  rw [lt_div_iff₀ hm2]
  have hfac : (T : ℝ) * (c_rev * D * ε) - (T : ℝ) * (D / 2 * m ^ 2 * ε ^ 2) =
      ((T : ℝ) * D * ε / 2) * (2 * c_rev - ε * m ^ 2) := by ring
  rw [hfac]
  have hpos : 0 < (T : ℝ) * D * ε / 2 := by positivity
  rw [mul_pos_iff_of_pos_left hpos]
  constructor <;> intro h <;> linarith

/-- **Mean-Reverting Regime Beats HODL Eventually:**
On any `T`-step path with step size `ε > 0` whose terminal displacement remains bounded
(`|u_T - u₀| ≤ B_band`), terminal IL vs. HODL `(D / 2) m^2 (u_T - u₀)^2` is `O(1)` while
cumulative revenue `T * c_rev * D * ε` grows linearly in `T`.
Hence for **any** `c_rev > 0`, cumulative revenue strictly beats terminal IL vs. HODL for all
`T > m^2 * B_band^2 / (2 * c_rev * ε)`. -/
theorem meanReverting_beats_hodl_eventually {D c_rev m ε B_band disp : ℝ}
    (hD : 0 < D) (hc : 0 < c_rev) (hε : 0 < ε)
    (hbound : |disp| ≤ B_band) {T : ℕ}
    (hT : m ^ 2 * B_band ^ 2 / (2 * c_rev * ε) < (T : ℝ)) :
    (D / 2) * m ^ 2 * disp ^ 2 < (T : ℝ) * (c_rev * D * ε) := by
  have hden : 0 < 2 * c_rev * ε := by positivity
  have hTmul : m ^ 2 * B_band ^ 2 < (T : ℝ) * (2 * c_rev * ε) := (div_lt_iff₀ hden).mp hT
  have hdisp2 : disp ^ 2 ≤ B_band ^ 2 := by
    have h0 : 0 ≤ B_band := le_trans (abs_nonneg disp) hbound
    rw [← sq_abs disp]
    exact pow_le_pow_left₀ (abs_nonneg disp) hbound 2
  have h1 : m ^ 2 * disp ^ 2 ≤ m ^ 2 * B_band ^ 2 :=
    mul_le_mul_of_nonneg_left hdisp2 (sq_nonneg m)
  have h2 : m ^ 2 * disp ^ 2 < (T : ℝ) * (2 * c_rev * ε) := lt_of_le_of_lt h1 hTmul
  have hmul := mul_lt_mul_of_pos_left h2 (by linarith : (0 : ℝ) < D / 2)
  linarith

/-- **Trending Regime Always Loses to HODL Eventually:**
On a monotone trending path (`|u_T - u₀| = T * ε`), terminal IL vs. HODL grows quadratically
as `T^2 * (D / 2) m^2 ε^2` while cumulative revenue grows linearly as `T * c_rev * D * ε`.
Hence for all `T > 2 * c_rev / (m^2 * ε)`, terminal IL strictly exceeds cumulative revenue. -/
theorem trending_loses_to_hodl_eventually {D c_rev m ε : ℝ}
    (hD : 0 < D) (hm : 0 < m) (hε : 0 < ε) {T : ℕ} (hTpos : 1 ≤ T)
    (hT : 2 * c_rev / (m ^ 2 * ε) < (T : ℝ)) :
    (T : ℝ) * (c_rev * D * ε) < (D / 2) * m ^ 2 * ((T : ℝ) * ε) ^ 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hden : 0 < m ^ 2 * ε := by positivity
  have hTmul : 2 * c_rev < (T : ℝ) * (m ^ 2 * ε) := (div_lt_iff₀ hden).mp hT
  have hfac : (D / 2) * m ^ 2 * ((T : ℝ) * ε) ^ 2 - (T : ℝ) * (c_rev * D * ε) =
      ((T : ℝ) * D * ε / 2) * ((T : ℝ) * (m ^ 2 * ε) - 2 * c_rev) := by ring
  have hpos : 0 < ((T : ℝ) * D * ε / 2) * ((T : ℝ) * (m ^ 2 * ε) - 2 * c_rev) := by
    have ha : 0 < (T : ℝ) * D * ε / 2 := by positivity
    have hb : 0 < (T : ℝ) * (m ^ 2 * ε) - 2 * c_rev := by linarith
    exact mul_pos ha hb
  linarith

/-- Terminal displacement of a `T`-step binary walk `path : Fin T → Bool` with steps `±ε`. -/
def walkDisplacement {T : ℕ} (ε : ℝ) (path : Fin T → Bool) : ℝ :=
  ∑ t : Fin T, if path t then ε else -ε

/-- Exact finite-probability second moment over all `2^T` symmetric binary paths:
`∑_{path ∈ {±ε}^T} (u_T - u₀)^2 = 2^T * T * ε^2`, i.e., `E[(u_T - u₀)^2] = T * ε^2`. -/
theorem sum_sq_walkDisplacement (T : ℕ) (ε : ℝ) :
    ∑ path : Fin T → Bool, (walkDisplacement ε path) ^ 2 =
      (2 : ℝ) ^ T * (T : ℝ) * ε ^ 2 := by
  induction T with
  | zero =>
    simp [walkDisplacement]
  | succ k ih =>
    let e : (Bool × (Fin k → Bool)) ≃ (Fin (k + 1) → Bool) :=
      (Fin.consEquiv (fun _ : Fin (k + 1) => Bool))
    rw [← Fintype.sum_equiv e
      (fun p => (walkDisplacement ε (e p)) ^ 2)
      (fun path => (walkDisplacement ε path) ^ 2)
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ (b : Bool) (rest : Fin k → Bool),
        walkDisplacement ε (e (b, rest)) = (if b then ε else -ε) + walkDisplacement ε rest := by
      intro b rest
      unfold walkDisplacement
      rw [Fin.sum_univ_succ]
      simp [e, Fin.consEquiv]
    simp_rw [hsplit]
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    have hpair : ∀ rest : Fin k → Bool,
        (ε + walkDisplacement ε rest) ^ 2 + (-ε + walkDisplacement ε rest) ^ 2 =
        2 * ε ^ 2 + 2 * (walkDisplacement ε rest) ^ 2 := fun rest => by ring
    rw [← Finset.sum_add_distrib]
    simp_rw [hpair, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool,
      nsmul_eq_mul, ih]
    push_cast
    ring

/-- **Symmetric Random-Walk Expected Net P&L vs. HODL:**
Under a fair `T`-step symmetric random walk (`±ε` each step), expected terminal IL vs. HODL
equals `T * (D / 2) * m^2 * ε^2` (matching `T`-step cumulative LVR identically), so expected
net P&L vs. HODL is strictly positive iff `ε < 2 * c_rev / m^2`. -/
theorem randomWalk_expected_netPnL_pos_iff {T : ℕ} (hT : 1 ≤ T)
    {D c_rev m ε : ℝ} (hD : 0 < D) (hm : 0 < m) (hε : 0 < ε) :
    let expectedIL :=
      (∑ path : Fin T → Bool, (D / 2) * m ^ 2 * (walkDisplacement ε path) ^ 2) / (2 : ℝ) ^ T
    0 < (T : ℝ) * (c_rev * D * ε) - expectedIL ↔
      ε < 2 * c_rev / m ^ 2 := by
  intro expectedIL
  have h2T : (2 : ℝ) ^ T ≠ 0 := by positivity
  have hE : expectedIL = (T : ℝ) * (D / 2 * m ^ 2 * ε ^ 2) := by
    dsimp [expectedIL]
    rw [← Finset.mul_sum, sum_sq_walkDisplacement]
    field_simp [h2T]
  rw [hE]
  exact multiperiod_lvr_regime_invariant hT hD hm hε

end MultiPeriodPriceRegimes

end Cascades
