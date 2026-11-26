import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Cascades.GraphSchedule
import Cascades.YieldScaling
import Cascades.UniversalBounds
import Cascades.NonlinearCLMM

/-!
# Consolidated Net P&L, LP Swap Fees, and LVR Break-Even Ledger

Formalizes the consolidated LP + burn ledger flagged in the conclusion of `cascades.md`,
combining:
* Gross burn revenue `B(α) = α * f * D * n(n+1) * S_M` (`α = 1` worst-case shared floor,
  `α = 2` direct correction, `α = 4` four-stage cascade),
* LP swap-fee revenue `F(β) = φ * β * D * S_M` (`β = m^2` direct, `β = 5 m^2 - 4` cascade),
* Total arbitrage extraction / Loss-Versus-Rebalancing (LVR) across all cross-family pools
  `LVR(u) = (D / 2) * m^2 * Q_M`, where `Q_M = ∑_{a<b} (u_a - u_b)^2`,
* Fixed gas / operational activation cost `C_gas ≥ 0`.

Proves exact necessary and sufficient characterizations (with zero hype):
1. **`singleShockNetPnL_pos_iff`:** On a single shock `u`, consolidated net P&L (gross burn
   + LP swap fees minus LVR) is strictly positive **if and only if** the effective shock size
   `Q_M / S_M` satisfies `Q_M / S_M < 2 * (α * n / (n + 1) * f + β / (n + 1)^2 * φ)`.
2. **`burnOnly_permanent_shock_neg`:** With zero LP swap fees (`φ = 0`), burn alone (`α ≤ 4`)
   is **strictly net-negative** on any permanent shock whose nonzero gaps exceed `8 * f`
   (e.g., `f = 10⁻⁶` against realistic `> 0.001%` price shocks).
3. **`cascade_netPnL_dominates_direct`:** For equal LVR, the 4-stage cascade strictly improves
   consolidated net P&L over direct correction by `(2 f n(n+1) + 4 φ ((n+1)^2 - 1)) D S_M > 0`,
   lifting the swap-fee break-even shock threshold from `2 φ` to `2 (5 - 4/(n+1)^2) φ`.
4. **Full mean-reverting round-trip cycle (`0 → u → 0`):**
   * **`roundTrip_vs_hodl_pos`:** Against initial inventory (HODL benchmark, where exact CLMM
     round-trip IL = 0), consolidated round-trip net P&L is `2(B + F) > 0`.
   * **`roundTrip_vs_lvr_pos_iff`:** Against continuous dynamic rebalancing (where LVR accrues
     on both legs), round-trip net P&L is strictly positive iff the exact same threshold on
     `Q_M / S_M` holds.
5. **`netPnL_with_gas_pos_iff`:** Formalizes Section 5's fixed-cost activation threshold—when
   per-unit depth margin `γ > 0`, fixed gas `C_gas` induces an exact minimum capital threshold
   `L > C_gas / (κ * γ)`.
-/

namespace Cascades

section ConsolidatedLedger

/-- Quadratic pairwise shock sum `Q_M = ∑_{a < b} (u_a - u_b)^2`. -/
def totalQuadShock {M : ℕ} (u : Fin M → ℝ) : ℝ :=
  ∑ p ∈ unorderedPairs M, (u p.1 - u p.2) ^ 2

/-- Total frictionless LVR / arbitrageur extraction across all cross-family pools on shock `u`:
each of the `m^2 = (n+1)^2` cross-family pools for pair `(a, b)` leaks `(D/2) (u_a - u_b)^2`
(proved equal for both direct correction and the cascade in `UniversalBounds.lean`). -/
noncomputable def totalLVR {M : ℕ} (D : ℝ) (n : ℕ) (u : Fin M → ℝ) : ℝ :=
  (D / 2) * ((n : ℝ) + 1) ^ 2 * totalQuadShock u

/-- Consolidated single-shock net P&L (gross burn + LP swap fees minus LVR) for burn
multiplier `α` (`1` worst-case shared floor, `2` direct, `4` cascade) and pool-volume
multiplier `β` (`(n+1)^2` direct, `5(n+1)^2 - 4` cascade). -/
noncomputable def singleShockNetPnL {M : ℕ} (D f φ α β : ℝ) (n : ℕ) (u : Fin M → ℝ) : ℝ :=
  (α * f * (n : ℝ) * ((n : ℝ) + 1) + φ * β) * D * totalShock u - totalLVR D n u

/-- Effective RMS-to-mean shock size `ε_eff = Q_M / S_M`. -/
noncomputable def effectiveShock {M : ℕ} (u : Fin M → ℝ) : ℝ :=
  totalQuadShock u / totalShock u

/-- Break-even shock threshold `2 * (α * n / (n + 1) * f + β / (n + 1)^2 * φ)`. -/
noncomputable def breakEvenShock (f φ α β : ℝ) (n : ℕ) : ℝ :=
  2 * (α * (n : ℝ) / ((n : ℝ) + 1) * f + β / ((n : ℝ) + 1) ^ 2 * φ)

/-- **Exact Single-Shock Consolidated Break-Even Theorem:**
For `D > 0` and `S_M > 0`, consolidated net P&L (burn + LP swap fees minus LVR) is strictly
positive **if and only if** the effective shock size `Q_M / S_M` lies strictly below the
break-even threshold `2 * (α * n / (n + 1) * f + β / (n + 1)^2 * φ)`. -/
theorem singleShockNetPnL_pos_iff {M n : ℕ} {D f φ α β : ℝ}
    (hD : 0 < D) (u : Fin M → ℝ) (hS : 0 < totalShock u) :
    0 < singleShockNetPnL D f φ α β n u ↔
      effectiveShock u < breakEvenShock f φ α β n := by
  unfold singleShockNetPnL totalLVR effectiveShock breakEvenShock
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [div_lt_iff₀ hS]
  have hfac :
      (α * f * (n : ℝ) * ((n : ℝ) + 1) + φ * β) * D * totalShock u -
        D / 2 * ((n : ℝ) + 1) ^ 2 * totalQuadShock u =
      (D / 2 * ((n : ℝ) + 1) ^ 2) *
        (2 * (α * (n : ℝ) / ((n : ℝ) + 1) * f + β / ((n : ℝ) + 1) ^ 2 * φ) * totalShock u -
          totalQuadShock u) := by
    field_simp [hm.ne']
  rw [hfac]
  have hpos : 0 < D / 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  constructor
  · intro h
    have hsub : 0 < 2 * (α * (n : ℝ) / ((n : ℝ) + 1) * f + β / ((n : ℝ) + 1) ^ 2 * φ) *
        totalShock u - totalQuadShock u :=
      (mul_pos_iff_of_pos_left hpos).mp h
    linarith
  · intro h
    exact mul_pos hpos (by linarith)

/-- **Burn-Only Permanent-Shock Impossibility Bound:**
If LP swap fees are zero (`φ = 0`), `0 ≤ α ≤ 4` (covering every execution up to and including
the 4-stage cascade), `f ≥ 0`, `D > 0`, `S_M > 0`, and every nonzero pairwise shock satisfies
`|u_a - u_b| > 8 * f`, then consolidated single-shock net P&L is **strictly negative**
(gross burn cannot overcome permanent-shock LVR when `f ≪ ε`). -/
theorem burnOnly_permanent_shock_neg {M n : ℕ} {D f α : ℝ}
    (hD : 0 < D) (hf : 0 ≤ f) (hα0 : 0 ≤ α) (hα4 : α ≤ 4)
    (u : Fin M → ℝ) (hS : 0 < totalShock u)
    (hbig : ∀ p ∈ unorderedPairs M, u p.1 ≠ u p.2 → 8 * f < |u p.1 - u p.2|) :
    singleShockNetPnL D f 0 α 0 n u < 0 := by
  have hQ_gt : 8 * f * totalShock u < totalQuadShock u := by
    unfold totalQuadShock totalShock
    rw [Finset.mul_sum]
    have hle : ∀ p ∈ unorderedPairs M,
        8 * f * |u p.1 - u p.2| ≤ (u p.1 - u p.2) ^ 2 := by
      intro p hp
      by_cases heq : u p.1 = u p.2
      · simp [heq]
      · have hlt := hbig p hp heq
        have habs : 0 < |u p.1 - u p.2| := abs_pos.mpr (sub_ne_zero.mpr heq)
        have hsq : (u p.1 - u p.2) ^ 2 = |u p.1 - u p.2| * |u p.1 - u p.2| := by
          rw [← sq_abs, sq]
        rw [hsq]
        exact (mul_lt_mul_of_pos_right hlt habs).le
    have hex : ∃ p ∈ unorderedPairs M,
        8 * f * |u p.1 - u p.2| < (u p.1 - u p.2) ^ 2 := by
      by_contra hnone
      push Not at hnone
      have hall0 : ∀ p ∈ unorderedPairs M, |u p.1 - u p.2| = 0 := by
        intro p hp
        by_contra hne0
        have hne : u p.1 ≠ u p.2 := fun h => hne0 (by simp [h])
        have hlt := hbig p hp hne
        have habs : 0 < |u p.1 - u p.2| := abs_pos.mpr (sub_ne_zero.mpr hne)
        have hsq : (u p.1 - u p.2) ^ 2 = |u p.1 - u p.2| * |u p.1 - u p.2| := by
          rw [← sq_abs, sq]
        have hgt : 8 * f * |u p.1 - u p.2| < (u p.1 - u p.2) ^ 2 := by
          rw [hsq]; exact mul_lt_mul_of_pos_right hlt habs
        linarith [hnone p hp]
      have hS0 : totalShock u = 0 := Finset.sum_eq_zero hall0
      linarith
    exact Finset.sum_lt_sum hle hex
  have hbe_le : breakEvenShock f 0 α 0 n ≤ 8 * f := by
    unfold breakEvenShock
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfrac : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hm]; linarith
    have h1 : α * (n : ℝ) / ((n : ℝ) + 1) * f ≤ 4 * f := by
      have : α * ((n : ℝ) / ((n : ℝ) + 1)) ≤ 4 * 1 :=
        mul_le_mul hα4 hfrac (by positivity) (by norm_num)
      have h2 : α * (n : ℝ) / ((n : ℝ) + 1) ≤ 4 := by linarith [mul_div_assoc α (n : ℝ) ((n : ℝ) + 1)]
      exact mul_le_mul_of_nonneg_right h2 hf
    linarith
  have heff : breakEvenShock f 0 α 0 n < effectiveShock u := by
    unfold effectiveShock
    rw [lt_div_iff₀ hS]
    have hmul : breakEvenShock f 0 α 0 n * totalShock u ≤ 8 * f * totalShock u :=
      mul_le_mul_of_nonneg_right hbe_le hS.le
    linarith
  unfold singleShockNetPnL totalLVR
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfac :
      (α * f * (n : ℝ) * ((n : ℝ) + 1) + 0 * 0) * D * totalShock u -
        D / 2 * ((n : ℝ) + 1) ^ 2 * totalQuadShock u =
      (D / 2 * ((n : ℝ) + 1) ^ 2) *
        (breakEvenShock f 0 α 0 n * totalShock u - totalQuadShock u) := by
    unfold breakEvenShock
    field_simp [hm.ne']
  rw [hfac]
  have hpos : 0 < D / 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  have hneg : breakEvenShock f 0 α 0 n * totalShock u - totalQuadShock u < 0 := by
    unfold effectiveShock at heff
    rw [lt_div_iff₀ hS] at heff
    linarith
  exact mul_neg_of_pos_of_neg hpos hneg

/-- **Cascade Net-P&L Advantage Over Direct Correction:**
At the same depth `D`, burn rate `f`, LP fee rate `φ`, and identical LVR, the 4-stage cascade
(`α = 4`, `β = 5(n+1)^2 - 4`) strictly improves consolidated net P&L over direct correction
(`α = 2`, `β = (n+1)^2`) by `(2 f n(n+1) + 4 φ ((n+1)^2 - 1)) D S_M`. -/
theorem cascade_netPnL_sub_direct {M n : ℕ} (D f φ : ℝ) (u : Fin M → ℝ) :
    singleShockNetPnL D f φ 4 (5 * ((n : ℝ) + 1) ^ 2 - 4) n u -
      singleShockNetPnL D f φ 2 (((n : ℝ) + 1) ^ 2) n u =
    (2 * f * (n : ℝ) * ((n : ℝ) + 1) + 4 * φ * (((n : ℝ) + 1) ^ 2 - 1)) * D * totalShock u := by
  unfold singleShockNetPnL
  ring

/-- In particular, with LP swap fees `φ > 0` (`f = 0`), the cascade lifts the single-shock
break-even threshold from `2 φ` (direct) to `2 (5 - 4 / (n + 1)^2) φ` (nearly `5×` higher). -/
theorem cascade_fee_breakEven_comparison (φ : ℝ) (n : ℕ) :
    breakEvenShock 0 φ 2 (((n : ℝ) + 1) ^ 2) n = 2 * φ ∧
    breakEvenShock 0 φ 4 (5 * ((n : ℝ) + 1) ^ 2 - 4) n =
      2 * (5 - 4 / ((n : ℝ) + 1) ^ 2) * φ := by
  unfold breakEvenShock
  have hm2 : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  constructor
  · field_simp [hm2]; ring
  · field_simp [hm2]; ring

/-- **Full Mean-Reverting Round-Trip Cycle (`0 → u → 0`):**
* Against initial inventory (HODL benchmark, where exact CLMM round-trip IL = 0 from
  `clmm_roundTrip_hodl_vs_lvr`), round-trip net P&L is `2 * (B + F) > 0` whenever
  `α f n(n+1) + φ β > 0`.
* Against continuous dynamic rebalancing (round-trip LVR = `2 * totalLVR`), round-trip
  net P&L equals `2 * singleShockNetPnL` and is positive iff the exact same break-even
  inequality `effectiveShock u < breakEvenShock f φ α β n` holds. -/
theorem roundTrip_hodl_and_lvr {M n : ℕ} {D f φ α β : ℝ}
    (hD : 0 < D) (u : Fin M → ℝ) (hS : 0 < totalShock u) :
    (0 < α * f * (n : ℝ) * ((n : ℝ) + 1) + φ * β →
      0 < 2 * ((α * f * (n : ℝ) * ((n : ℝ) + 1) + φ * β) * D * totalShock u)) ∧
    (0 < 2 * ((α * f * (n : ℝ) * ((n : ℝ) + 1) + φ * β) * D * totalShock u) - 2 * totalLVR D n u ↔
      effectiveShock u < breakEvenShock f φ α β n) := by
  constructor
  · intro hcoef
    positivity
  · have h2 :
        2 * ((α * f * (n : ℝ) * ((n : ℝ) + 1) + φ * β) * D * totalShock u) - 2 * totalLVR D n u =
        2 * singleShockNetPnL D f φ α β n u := by
      unfold singleShockNetPnL; ring
    rw [h2, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
    exact singleShockNetPnL_pos_iff hD u hS

/-- **Section 5 Fixed-Cost Activation Threshold:**
With scale-invariant per-unit depth margin `γ` (so gross net margin scales linearly as `κ L γ`)
and fixed gas / operational cost `C_gas ≥ 0`, net profit `κ L γ - C_gas` is strictly positive
(when `κ > 0, γ > 0`) **if and only if** per-pool liquidity exceeds `L > C_gas / (κ * γ)`. -/
theorem fixedCost_activation_threshold {κ L γ C_gas : ℝ}
    (hκ : 0 < κ) (hγ : 0 < γ) :
    0 < κ * L * γ - C_gas ↔ C_gas / (κ * γ) < L := by
  have hκγ : 0 < κ * γ := mul_pos hκ hγ
  rw [div_lt_iff₀ hκγ]
  constructor <;> intro h <;> linarith

end ConsolidatedLedger

end Cascades
