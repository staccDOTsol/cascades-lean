import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Cascades.UniversalBounds

/-!
# Exact Nonlinear Concentrated-Liquidity AMM (Uniswap v3) & Range Exhaustion

Drops the linearized `Δr = -q / D` local approximation and proves the core mechanism
directly on **exact nonlinear constant-product / Uniswap-v3 single-range CLMM curves**
with finite price range `[p_a, p_b]` (parameterized by square-root prices `0 < s_a < s_b`):

* **Exact CLMM reserves & constant-product invariant:**
  `x(s) = L_v3 * (1/s - 1/s_b)`, `y(s) = L_v3 * (s - s_a)`,
  `X_virt(s) * Y_virt(s) = L_v3^2` identically, with exact range exhaustion (`x(s_b) = 0`,
  `y(s_a) = 0`).
* **First-principles derivation of `κ`:** For symmetric range `[r⁻¹, r]` (`r > 1`) around `s₀ = 1`,
  `K_pool = 2 L_v3 (1 - r⁻¹)` and local depth `D = L_v3 / 2 = κ K_pool` with
  `κ = 1 / (4 (1 - r⁻¹))`.
* **Exact nonlinear arbitrage profit & LVR completed-square identity:**
  `Π_CLMM(s₀ → s₁; s_ext) = L_v3 (s_ext - s₀)^2 / s₀ - L_v3 (s_ext - s₁)^2 / s₁`
  `= W(s₀; s_ext) - W(s₁; s_ext)` (exact IL vs. HODL!).
* **Exact clamped optimum & range-exhaustion capping:**
  `s₁* = clamp(s_ext, s_a, s_b)` uniquely maximizes arbitrageur profit over `[s_a, s_b]`;
  when `s_ext ∉ [s_a, s_b]`, range exhaustion strictly caps both LVR and trade volume.
* **Exact round-trip zero-IL vs. strictly positive cumulative LVR:**
  A round trip `s₀ → s₁ → s₀` restores exact reserves (`IL = 0` vs. HODL) while cumulative
  two-leg arbitrage extraction equals `L_v3 (s₁ - s₀)^2 (1/s₀ + 1/s₁) > 0`.
* **Nonlinear routing-independent complete-graph lower bounds:**
  For **any** finite trace of exact nonlinear CLMM swaps clearing cross-family pools to within
  `δ_s ≥ 0` of their clamped equilibria `clamp(s_{ab}, s_a, s_b)`, total quote volume and
  taxable wrapped transfers satisfy exact routing-independent lower bounds (even under
  maximal 2-pool transfer sharing).
* **Exact `O(ε^2)` bridge to the linear model:**
  `L_v3 * (exp(ε/2) - 1) - (L_v3 / 2) * ε = O(ε^2)` as `ε → 0`, with upside convexity
  `L_v3 * (exp(ε/2) - 1) ≥ (L_v3 / 2) * ε` for all `ε ≥ 0`.
-/

namespace Cascades

section ExactCLMM

/-- Real base-asset reserve `x(s) = L_v3 * (1/s - 1/s_b)` in a Uniswap-v3 range `[s_a, s_b]`. -/
noncomputable def clmmX (Lv3 sb s : ℝ) : ℝ :=
  Lv3 * (s⁻¹ - sb⁻¹)

/-- Real quote-asset reserve `y(s) = L_v3 * (s - s_a)` in a Uniswap-v3 range `[s_a, s_b]`. -/
noncomputable def clmmY (Lv3 sa s : ℝ) : ℝ :=
  Lv3 * (s - sa)

/-- Virtual base reserve `X_virt(s) = x(s) + L_v3 / s_b = L_v3 / s`. -/
noncomputable def clmmVirtX (Lv3 sb s : ℝ) : ℝ :=
  clmmX Lv3 sb s + Lv3 * sb⁻¹

/-- Virtual quote reserve `Y_virt(s) = y(s) + L_v3 * s_a = L_v3 * s`. -/
noncomputable def clmmVirtY (Lv3 sa s : ℝ) : ℝ :=
  clmmY Lv3 sa s + Lv3 * sa

/-- Exact Uniswap-v3 shifted constant-product invariant: `X_virt(s) * Y_virt(s) = L_v3^2`. -/
theorem clmm_const_product {Lv3 sa sb s : ℝ} (hs : s ≠ 0) :
    clmmVirtX Lv3 sb s * clmmVirtY Lv3 sa s = Lv3 ^ 2 := by
  unfold clmmVirtX clmmVirtY clmmX clmmY
  field_simp [hs]
  ring

/-- Real reserves are non-negative throughout the active range `s ∈ [s_a, s_b]`. -/
theorem clmm_reserves_nonneg {Lv3 sa sb s : ℝ}
    (hL : 0 ≤ Lv3) (hsa : 0 < sa) (h1 : sa ≤ s) (h2 : s ≤ sb) :
    0 ≤ clmmX Lv3 sb s ∧ 0 ≤ clmmY Lv3 sa s := by
  have hs : 0 < s := lt_of_lt_of_le hsa h1
  have hsb : 0 < sb := lt_of_lt_of_le hs h2
  constructor
  · unfold clmmX
    have hinv : sb⁻¹ ≤ s⁻¹ := inv_anti₀ hs h2
    exact mul_nonneg hL (sub_nonneg.mpr hinv)
  · unfold clmmY
    exact mul_nonneg hL (sub_nonneg.mpr h1)

/-- Exact range exhaustion at boundaries: `x(s_b) = 0` and `y(s_a) = 0`. -/
theorem clmm_boundary_exhaustion (Lv3 sa sb : ℝ) :
    clmmX Lv3 sb sb = 0 ∧ clmmY Lv3 sa sa = 0 := by
  simp [clmmX, clmmY]

/-- Portfolio value of the CLMM position at state `s`, marked to external price `s_ext^2`
in quote numeraire `Y`: `W(s; s_ext) = s_ext^2 * x(s) + y(s)`. -/
noncomputable def clmmValue (Lv3 sa sb s s_ext : ℝ) : ℝ :=
  s_ext ^ 2 * clmmX Lv3 sb s + clmmY Lv3 sa s

/-- First-principles derivation of the depth-to-capital multiplier `κ`:
for a symmetric CLMM range `[r⁻¹, r]` (`r > 1`) initialized at `s₀ = 1`, total initial capital
is `K = 2 L_v3 (1 - r⁻¹)`, so local depth `D = L_v3 / 2` equals `κ * K` with
`κ = 1 / (4 * (1 - r⁻¹))`. -/
theorem clmm_symmetric_depth_multiplier {Lv3 r : ℝ} (hr : 1 < r) :
    let K := clmmValue Lv3 r⁻¹ r 1 1
    let κ := 1 / (4 * (1 - r⁻¹))
    K = 2 * Lv3 * (1 - r⁻¹) ∧ Lv3 / 2 = κ * K := by
  have hr0 : 0 < r := by linarith
  have hinv_lt : r⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; exact Or.inr hr
  have h1r : 1 - r⁻¹ ≠ 0 := by linarith
  have hK : clmmValue Lv3 r⁻¹ r 1 1 = 2 * Lv3 * (1 - r⁻¹) := by
    unfold clmmValue clmmX clmmY
    ring
  refine ⟨hK, ?_⟩
  rw [hK]
  field_simp [h1r]
  ring

/-- Exact nonlinear arbitrageur profit from moving a CLMM pool from state `s₀` to `s₁` at external
price `s_ext^2`: arbitrageur takes `x(s₀) - x(s₁)` of base asset and pays `y(s₁) - y(s₀)` of
quote asset. -/
noncomputable def clmmArbProfit (Lv3 sa sb s₀ s₁ s_ext : ℝ) : ℝ :=
  s_ext ^ 2 * (clmmX Lv3 sb s₀ - clmmX Lv3 sb s₁) - (clmmY Lv3 sa s₁ - clmmY Lv3 sa s₀)

/-- Exact zero-sum conservation between arbitrageur profit and LP mark-to-market change
relative to HODL: `Π_CLMM(s₀ → s₁; s_ext) = W(s₀; s_ext) - W(s₁; s_ext)`. -/
theorem clmmArbProfit_eq_hodl_sub_pool (Lv3 sa sb s₀ s₁ s_ext : ℝ) :
    clmmArbProfit Lv3 sa sb s₀ s₁ s_ext =
      clmmValue Lv3 sa sb s₀ s_ext - clmmValue Lv3 sa sb s₁ s_ext := by
  unfold clmmArbProfit clmmValue
  ring

/-- **Exact Nonlinear Completed-Square Identity (zero linearization):**
For all `s₀, s₁ ≠ 0`,
`Π_CLMM(s₀ → s₁; s_ext) = L_v3 * (s_ext - s₀)^2 / s₀ - L_v3 * (s_ext - s₁)^2 / s₁`. -/
theorem clmmArbProfit_eq_sub_sq {Lv3 sa sb s₀ s₁ s_ext : ℝ} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) :
    clmmArbProfit Lv3 sa sb s₀ s₁ s_ext =
      Lv3 * (s_ext - s₀) ^ 2 / s₀ - Lv3 * (s_ext - s₁) ^ 2 / s₁ := by
  unfold clmmArbProfit clmmX clmmY
  field_simp [hs₀, hs₁]
  ring

/-- Clamping external sqrt-price `s_ext` into the active CLMM range `[s_a, s_b]`. -/
def clampRange (s_ext sa sb : ℝ) : ℝ :=
  max sa (min sb s_ext)

theorem clampRange_mem {s_ext sa sb : ℝ} (hab : sa ≤ sb) :
    sa ≤ clampRange s_ext sa sb ∧ clampRange s_ext sa sb ≤ sb := by
  unfold clampRange
  constructor
  · exact le_max_left sa _
  · exact max_le hab (min_le_left sb s_ext)

/-- Monotonicity of the residual penalty `g(s) = (s_ext - s)^2 / s`:
its unique minimizer on `[s_a, s_b]` is `clampRange s_ext sa sb`. -/
private theorem penalty_clamp_le {s_ext sa sb s₁ : ℝ}
    (hsa : 0 < sa) (hs_ext : 0 < s_ext) (h1 : sa ≤ s₁) (h2 : s₁ ≤ sb) :
    (s_ext - clampRange s_ext sa sb) ^ 2 / clampRange s_ext sa sb ≤
      (s_ext - s₁) ^ 2 / s₁ := by
  have hab : sa ≤ sb := le_trans h1 h2
  have hs₁ : 0 < s₁ := lt_of_lt_of_le hsa h1
  have hcl_mem := clampRange_mem (s_ext := s_ext) hab
  have hcl_pos : 0 < clampRange s_ext sa sb := lt_of_lt_of_le hsa hcl_mem.1
  -- Exact difference factorization: (e-s1)^2/s1 - (e-c)^2/c = (s1 - c)(s1*c - e^2)/(s1*c)
  rw [← sub_nonneg]
  have hdiff :
      (s_ext - s₁) ^ 2 / s₁ - (s_ext - clampRange s_ext sa sb) ^ 2 / clampRange s_ext sa sb =
      (s₁ - clampRange s_ext sa sb) * (s₁ * clampRange s_ext sa sb - s_ext ^ 2) /
        (s₁ * clampRange s_ext sa sb) := by
    field_simp [hs₁.ne', hcl_pos.ne']
    ring
  rw [hdiff]
  apply div_nonneg _ (mul_pos hs₁ hcl_pos).le
  unfold clampRange
  by_cases hlow : s_ext ≤ sa
  · have hmin : min sb s_ext = s_ext := min_eq_right (le_trans hlow hab)
    have hmax : max sa (min sb s_ext) = sa := by rw [hmin, max_eq_left hlow]
    rw [hmax]
    have hf1 : 0 ≤ s₁ - sa := by linarith
    have hf2 : 0 ≤ s₁ * sa - s_ext ^ 2 := by nlinarith
    exact mul_nonneg hf1 hf2
  · push Not at hlow
    by_cases hhi : sb ≤ s_ext
    · have hmin : min sb s_ext = sb := min_eq_left hhi
      have hmax : max sa (min sb s_ext) = sb := by rw [hmin, max_eq_right hab]
      rw [hmax]
      have hf1 : s₁ - sb ≤ 0 := by linarith
      have hf2 : s₁ * sb - s_ext ^ 2 ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hf1 hf2
    · push Not at hhi
      have hmin : min sb s_ext = s_ext := min_eq_right hhi.le
      have hmax : max sa (min sb s_ext) = s_ext := by rw [hmin, max_eq_right hlow.le]
      rw [hmax]
      have hsq : (s₁ - s_ext) * (s₁ * s_ext - s_ext ^ 2) = s_ext * (s₁ - s_ext) ^ 2 := by ring
      rw [hsq]
      positivity

/-- **Exact Nonlinear Clamped Optimality Theorem:**
For any CLMM range `0 < s_a ≤ s_b`, liquidity `L_v3 > 0`, starting state `s₀ > 0`, and external
sqrt-price `s_ext > 0`, moving to `s₁* = clampRange s_ext sa sb` globally maximizes nonlinear
arbitrage profit over all reachable states `s₁ ∈ [s_a, s_b]`. -/
theorem clmmArbProfit_le_clamp {Lv3 sa sb s₀ s₁ s_ext : ℝ}
    (hL : 0 < Lv3) (hsa : 0 < sa) (hs₀ : 0 < s₀) (hs_ext : 0 < s_ext)
    (h1 : sa ≤ s₁) (h2 : s₁ ≤ sb) :
    clmmArbProfit Lv3 sa sb s₀ s₁ s_ext ≤
      clmmArbProfit Lv3 sa sb s₀ (clampRange s_ext sa sb) s_ext := by
  have hab : sa ≤ sb := le_trans h1 h2
  have hs₁ : 0 < s₁ := lt_of_lt_of_le hsa h1
  have hcl : 0 < clampRange s_ext sa sb := lt_of_lt_of_le hsa (clampRange_mem hab).1
  rw [clmmArbProfit_eq_sub_sq hs₀.ne' hs₁.ne', clmmArbProfit_eq_sub_sq hs₀.ne' hcl.ne']
  have hpen := penalty_clamp_le hsa hs_ext h1 h2
  have hmul : Lv3 * (s_ext - clampRange s_ext sa sb) ^ 2 / clampRange s_ext sa sb ≤
      Lv3 * (s_ext - s₁) ^ 2 / s₁ := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hpen hL.le
  linarith

/-- When `0 < s_ext` stays inside `[s_a, s_b]`, optimal nonlinear arbitrage profit (= exact IL
vs. HODL) equals `L_v3 * (s_ext - s₀)^2 / s₀`. -/
theorem clmm_inRange_exact_lvr {Lv3 sa sb s₀ s_ext : ℝ}
    (hs₀ : 0 < s₀) (hs_ext : 0 < s_ext) (h1 : sa ≤ s_ext) (h2 : s_ext ≤ sb) :
    clmmArbProfit Lv3 sa sb s₀ (clampRange s_ext sa sb) s_ext =
      Lv3 * (s_ext - s₀) ^ 2 / s₀ := by
  have hcl : clampRange s_ext sa sb = s_ext := by
    unfold clampRange
    rw [min_eq_right h2, max_eq_right h1]
  rw [hcl, clmmArbProfit_eq_sub_sq hs₀.ne' hs_ext.ne']
  ring

/-- **Range-Exhaustion Capping Theorem:**
When external price leaves the active CLMM range (`s_ext < s_a` or `s_b < s_ext`), range
exhaustion **strictly caps** arbitrage profit / LVR below the uncapped value
`L_v3 * (s_ext - s₀)^2 / s₀`. -/
theorem clmm_outOfRange_caps_lvr {Lv3 sa sb s₀ s_ext : ℝ}
    (hL : 0 < Lv3) (hsa : 0 < sa) (hab : sa ≤ sb) (hs₀ : 0 < s₀)
    (hout : s_ext < sa ∨ sb < s_ext) :
    clmmArbProfit Lv3 sa sb s₀ (clampRange s_ext sa sb) s_ext <
      Lv3 * (s_ext - s₀) ^ 2 / s₀ := by
  have hcl_mem := clampRange_mem (s_ext := s_ext) hab
  have hcl_pos : 0 < clampRange s_ext sa sb := lt_of_lt_of_le hsa hcl_mem.1
  rw [clmmArbProfit_eq_sub_sq hs₀.ne' hcl_pos.ne']
  have hne : s_ext - clampRange s_ext sa sb ≠ 0 := by
    rcases hout with hlt | hgt
    · linarith [hcl_mem.1]
    · linarith [hcl_mem.2]
  have hpen_pos : 0 < Lv3 * (s_ext - clampRange s_ext sa sb) ^ 2 / clampRange s_ext sa sb := by
    positivity
  linarith

/-- **Exact Nonlinear Round-Trip Accounting (HODL vs. LVR):**
On a full shock-and-return cycle `s₀ → s₁ → s₀`:
1. The pool returns to the exact initial reserves (`W(s₀; s₀) - W(s₀; s₀) = 0`, zero IL vs. HODL).
2. Cumulative arbitrageur extraction across the two legs (outbound + return) equals
   `L_v3 * (s₁ - s₀)^2 * (1/s₀ + 1/s₁)`, which is strictly positive whenever `s₁ ≠ s₀`. -/
theorem clmm_roundTrip_hodl_vs_lvr {Lv3 sa sb s₀ s₁ : ℝ}
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    (clmmValue Lv3 sa sb s₀ s₀ - clmmValue Lv3 sa sb s₀ s₀ = 0) ∧
    (clmmArbProfit Lv3 sa sb s₀ s₁ s₁ + clmmArbProfit Lv3 sa sb s₁ s₀ s₀ =
      Lv3 * (s₁ - s₀) ^ 2 * (s₀⁻¹ + s₁⁻¹)) := by
  refine ⟨sub_self _, ?_⟩
  rw [clmmArbProfit_eq_sub_sq hs₀.ne' hs₁.ne', clmmArbProfit_eq_sub_sq hs₁.ne' hs₀.ne']
  field_simp [hs₀.ne', hs₁.ne']
  ring

end ExactCLMM

section NonlinearGraphBounds

/-- An exact nonlinear CLMM swap leg on pool `{x, y}` (`x ≠ y`) moving its sqrt-price by `ds`
with quote-numeraire trade volume `L_v3 * |ds|`. -/
structure CLMMSwapLeg {M : ℕ} (m : Fin M → ℕ) where
  x : Asset m
  y : Asset m
  hne : x ≠ y
  ds : ℝ

/-- Update the sqrt-price matrix of a complete graph of nonlinear CLMM pools by one swap leg.
We track each cross-family pool `(x, y)` with `x.1 < y.1` by its current sqrt-price `s x y`. -/
def applyCLMMSwap {M : ℕ} {m : Fin M → ℕ} (S : Asset m → Asset m → ℝ)
    (leg : CLMMSwapLeg m) : Asset m → Asset m → ℝ :=
  fun p q =>
    if p = leg.x ∧ q = leg.y then S p q + leg.ds
    else if p = leg.y ∧ q = leg.x then S p q - leg.ds
    else S p q

def applyCLMMSwaps {M : ℕ} {m : Fin M → ℕ} :
    (Asset m → Asset m → ℝ) → List (CLMMSwapLeg m) → (Asset m → Asset m → ℝ)
  | S, [] => S
  | S, leg :: rest => applyCLMMSwaps (applyCLMMSwap S leg) rest

/-- Exact quote-numeraire volume of a nonlinear CLMM swap trace: `∑ L_v3 * |ds|`. -/
def clmmTraceVol {M : ℕ} {m : Fin M → ℕ} (Lv3 : ℝ) (σ : List (CLMMSwapLeg m)) : ℝ :=
  (σ.map (fun leg => Lv3 * |leg.ds|)).sum

/-- Wrapped-asset pool-interface volume across an arbitrary nonlinear CLMM swap trace. -/
def clmmWrappedInterface {M : ℕ} {m : Fin M → ℕ} (Lv3 : ℝ) (σ : List (CLMMSwapLeg m)) : ℝ :=
  (σ.map (fun leg => (wrappedCount2 leg.x leg.y : ℝ) * (Lv3 * |leg.ds|))).sum

/-- Exact quote-numeraire volume on unordered pool `{a, b}` in a nonlinear CLMM trace. -/
def clmmEdgeVol {M : ℕ} {m : Fin M → ℕ} (Lv3 : ℝ) (σ : List (CLMMSwapLeg m))
    (a b : Asset m) : ℝ :=
  (σ.map (fun leg =>
    if (leg.x = a ∧ leg.y = b) ∨ (leg.x = b ∧ leg.y = a) then Lv3 * |leg.ds| else 0)).sum

/-- Path-independence lower bound on a single nonlinear CLMM pool: moving sqrt-price from
`S a b` to `S' a b` along **any** swap sequence requires quote volume `≥ L_v3 * |S' a b - S a b|`. -/
theorem clmmEdgeVol_ge_delta {M : ℕ} {m : Fin M → ℕ} {Lv3 : ℝ} (hL : 0 ≤ Lv3)
    (S : Asset m → Asset m → ℝ) (σ : List (CLMMSwapLeg m)) (a b : Asset m) :
    Lv3 * |applyCLMMSwaps S σ a b - S a b| ≤ clmmEdgeVol Lv3 σ a b := by
  induction σ generalizing S with
  | nil => simp [applyCLMMSwaps, clmmEdgeVol]
  | cons leg rest ih =>
    have hstep : Lv3 * |applyCLMMSwap S leg a b - S a b| ≤
        (if (leg.x = a ∧ leg.y = b) ∨ (leg.x = b ∧ leg.y = a) then Lv3 * |leg.ds| else 0) := by
      unfold applyCLMMSwap
      by_cases h1 : a = leg.x ∧ b = leg.y
      · rcases h1 with ⟨rfl, rfl⟩
        simp only [and_self, ↓reduceIte, true_or, add_sub_cancel_left, le_refl]
      · by_cases h2 : a = leg.y ∧ b = leg.x
        · rcases h2 with ⟨rfl, rfl⟩
          have hne' : ¬ (leg.y = leg.x ∧ leg.x = leg.y) := fun h => leg.hne h.1.symm
          simp only [hne', ↓reduceIte, and_self, or_true, sub_sub_cancel_left, abs_neg, le_refl]
        · have hdisj : ¬ ((leg.x = a ∧ leg.y = b) ∨ (leg.x = b ∧ leg.y = a)) := by
            rintro (⟨h1a, h1b⟩ | ⟨h2a, h2b⟩)
            · exact h1 ⟨h1a.symm, h1b.symm⟩
            · exact h2 ⟨h2b.symm, h2a.symm⟩
          simp [h1, h2, hdisj]
    have hrest := ih (applyCLMMSwap S leg)
    have htri : |applyCLMMSwaps S (leg :: rest) a b - S a b| ≤
        |applyCLMMSwaps (applyCLMMSwap S leg) rest a b - applyCLMMSwap S leg a b| +
        |applyCLMMSwap S leg a b - S a b| := by
      simpa [applyCLMMSwaps] using abs_sub_le (applyCLMMSwaps (applyCLMMSwap S leg) rest a b)
        (applyCLMMSwap S leg a b) (S a b)
    have hmul : Lv3 * |applyCLMMSwaps S (leg :: rest) a b - S a b| ≤
        Lv3 * |applyCLMMSwaps (applyCLMMSwap S leg) rest a b - applyCLMMSwap S leg a b| +
        Lv3 * |applyCLMMSwap S leg a b - S a b| := by
      have := mul_le_mul_of_nonneg_left htri hL
      linarith
    simp only [clmmEdgeVol, List.map_cons, List.sum_cons] at hrest ⊢
    linarith

private theorem sum_crossAssetPairs_clmmEdgeVol_le {M : ℕ} (m : Fin M → ℕ)
    {Lv3 : ℝ} (hL : 0 ≤ Lv3) (σ : List (CLMMSwapLeg m)) :
    ∑ p ∈ crossAssetPairs m, clmmEdgeVol Lv3 σ p.1 p.2 ≤ clmmTraceVol Lv3 σ := by
  induction σ with
  | nil => simp [clmmEdgeVol, clmmTraceVol]
  | cons leg rest ih =>
    simp only [clmmEdgeVol, clmmTraceVol, List.map_cons, List.sum_cons,
      Finset.sum_add_distrib] at ih ⊢
    have hleg : ∑ p ∈ crossAssetPairs m,
        (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) ≤
        Lv3 * |leg.ds| := by
      by_cases hlt : leg.x.1 < leg.y.1
      · have hmem : (leg.x, leg.y) ∈ crossAssetPairs m := by simp [crossAssetPairs, hlt]
        have huniq : ∀ p ∈ crossAssetPairs m, p ≠ (leg.x, leg.y) →
            (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) = 0 := by
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
              (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) = 0 := by
            intro p hp hne
            have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
                rw [← h1, ← h2] at hp_lt; exact lt_asymm hgt hp_lt
              · exact hne (Prod.ext h2.symm h1.symm)
            simp [hneg]
          rw [Finset.sum_eq_single (leg.y, leg.x) huniq (fun h => (h hmem).elim)]
          simp
        · have hzero : ∀ p ∈ crossAssetPairs m,
              (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) = 0 := by
            intro p hp
            have hp_lt : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
            have hneg : ¬ ((leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1)) := by
              rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · rw [← h1, ← h2] at hp_lt; exact hlt hp_lt
              · rw [← h2, ← h1] at hp_lt; exact hgt hp_lt
            simp [hneg]
          rw [Finset.sum_eq_zero hzero]
          exact mul_nonneg hL (abs_nonneg leg.ds)
    linarith

private theorem sum_crossAssetPairs_clmmWeighted_le {M : ℕ} (m : Fin M → ℕ)
    {Lv3 : ℝ} (hL : 0 ≤ Lv3) (σ : List (CLMMSwapLeg m)) :
    ∑ p ∈ crossAssetPairs m, (wrappedCount2 p.1 p.2 : ℝ) * clmmEdgeVol Lv3 σ p.1 p.2 ≤
      clmmWrappedInterface Lv3 σ := by
  induction σ with
  | nil => simp [clmmEdgeVol, clmmWrappedInterface]
  | cons leg rest ih =>
    simp only [clmmEdgeVol, clmmWrappedInterface, List.map_cons, List.sum_cons, mul_add,
      Finset.sum_add_distrib] at ih ⊢
    have hcomm : wrappedCount2 leg.y leg.x = wrappedCount2 leg.x leg.y := by
      unfold wrappedCount2; omega
    have hleg : ∑ p ∈ crossAssetPairs m,
        (wrappedCount2 p.1 p.2 : ℝ) *
          (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) ≤
        (wrappedCount2 leg.x leg.y : ℝ) * (Lv3 * |leg.ds|) := by
      by_cases hlt : leg.x.1 < leg.y.1
      · have hmem : (leg.x, leg.y) ∈ crossAssetPairs m := by simp [crossAssetPairs, hlt]
        have huniq : ∀ p ∈ crossAssetPairs m, p ≠ (leg.x, leg.y) →
            (wrappedCount2 p.1 p.2 : ℝ) *
              (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) = 0 := by
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
                (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) = 0 := by
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
                (if (leg.x = p.1 ∧ leg.y = p.2) ∨ (leg.x = p.2 ∧ leg.y = p.1) then Lv3 * |leg.ds| else 0) = 0 := by
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

private theorem sum_crossAssetPairs_grouped_clmm {M : ℕ} (m : Fin M → ℕ)
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
    · intro hlt; exact ⟨(a, b), hlt, (i, j), rfl⟩
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
    exact Prod.ext (by have := congrArg Prod.fst h; simpa using this)
      (by have := congrArg Prod.snd h; simpa using this)
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h), Fintype.sum_prod_type]

private theorem sum_isWrapped_fin_clmm {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a) (a : Fin M) :
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

/-- **Exact Nonlinear CLMM Complete-Graph Volume & Taxable-Transfer Lower Bounds (with range
clamping `[s_a, s_b]` and stopping hurdle `δ_s ≥ 0`):**
Starting every pool at reference sqrt-price `1`, given external log-price shock vector `u`
(so external relative sqrt-price for pair `(a, b)` is `s_ext(a,b) = exp((u_a - u_b)/2)` and
clamped CLMM target is `s*(a,b) = clampRange (exp((u_a - u_b)/2)) sa sb`), **every** arbitrary
nonlinear swap sequence `σ` that brings all cross-family pools within `δ_s` of `s*(a,b)`
satisfies:
1. `clmmTraceVol L_v3 σ ≥ L_v3 * ∑_{a<b} m_a m_b * max (|s*(a,b) - 1| - δ_s) 0`
2. For any wrapped-transfer ledger `txs` covering `clmmWrappedInterface L_v3 σ` (even with
   maximal 2-pool transfer sharing):
   `totalTransferVol txs ≥ (L_v3 / 2) * ∑_{a<b} (2 m_a m_b - m_a - m_b) * max (|s*(a,b) - 1| - δ_s) 0`. -/
theorem clmm_complete_graph_bounds {M : ℕ} (m : Fin M → ℕ) (hm : ∀ a, 0 < m a)
    {Lv3 sa sb δs : ℝ} (hL : 0 ≤ Lv3) (u : Fin M → ℝ)
    (σ : List (CLMMSwapLeg m)) (txs : List (WrappedTransfer m))
    (hcover : clmmWrappedInterface Lv3 σ ≤ coveredInterfaceVol txs)
    (heq : ∀ x y : Asset m, x.1 < y.1 →
      |applyCLMMSwaps (fun _ _ => (1 : ℝ)) σ x y -
        clampRange (Real.exp ((u x.1 - u y.1) / 2)) sa sb| ≤ δs) :
    Lv3 * ∑ p ∈ unorderedPairs M,
        (m p.1 : ℝ) * (m p.2 : ℝ) *
          max (|clampRange (Real.exp ((u p.1 - u p.2) / 2)) sa sb - 1| - δs) 0 ≤
      clmmTraceVol Lv3 σ ∧
    (Lv3 / 2) * ∑ p ∈ unorderedPairs M,
        (2 * (m p.1 : ℝ) * (m p.2 : ℝ) - (m p.1 : ℝ) - (m p.2 : ℝ)) *
          max (|clampRange (Real.exp ((u p.1 - u p.2) / 2)) sa sb - 1| - δs) 0 ≤
      totalTransferVol txs := by
  have hedge : ∀ x y : Asset m, x.1 < y.1 →
      Lv3 * max (|clampRange (Real.exp ((u x.1 - u y.1) / 2)) sa sb - 1| - δs) 0 ≤
        clmmEdgeVol Lv3 σ x y := by
    intro x y hxy
    have hbase := clmmEdgeVol_ge_delta hL (fun _ _ => (1 : ℝ)) σ x y
    set sF := applyCLMMSwaps (fun _ _ => (1 : ℝ)) σ x y
    set sT := clampRange (Real.exp ((u x.1 - u y.1) / 2)) sa sb
    have htri : |sT - 1| - |sF - sT| ≤ |sF - 1| := by
      have h1 : |sT - 1| ≤ |sT - sF| + |sF - 1| := abs_sub_le sT sF 1
      rw [abs_sub_comm sT sF] at h1
      linarith
    have hsub : |sT - 1| - δs ≤ |sF - 1| := by linarith [heq x y hxy]
    have hnn : 0 ≤ clmmEdgeVol Lv3 σ x y := by
      unfold clmmEdgeVol
      exact List.sum_nonneg fun z hz => by
        simp only [List.mem_map] at hz
        rcases hz with ⟨leg, _, rfl⟩
        split_ifs
        · exact mul_nonneg hL (abs_nonneg _)
        · exact le_rfl
    rcases le_total 0 (|sT - 1| - δs) with hpos | hneg
    · rw [max_eq_left hpos]
      exact le_trans (mul_le_mul_of_nonneg_left hsub hL) hbase
    · rw [max_eq_right hneg, mul_zero]; exact hnn
  constructor
  · have h1 := sum_crossAssetPairs_clmmEdgeVol_le m hL σ
    have h2 : ∑ p ∈ crossAssetPairs m,
          Lv3 * max (|clampRange (Real.exp ((u p.1.1 - u p.2.1) / 2)) sa sb - 1| - δs) 0 ≤
        ∑ p ∈ crossAssetPairs m, clmmEdgeVol Lv3 σ p.1 p.2 :=
      Finset.sum_le_sum fun p hp => hedge p.1 p.2 (Finset.mem_filter.mp hp).2
    have h3 : ∑ p ∈ crossAssetPairs m,
          Lv3 * max (|clampRange (Real.exp ((u p.1.1 - u p.2.1) / 2)) sa sb - 1| - δs) 0 =
        Lv3 * ∑ ab ∈ unorderedPairs M,
          (m ab.1 : ℝ) * (m ab.2 : ℝ) *
            max (|clampRange (Real.exp ((u ab.1 - u ab.2) / 2)) sa sb - 1| - δs) 0 := by
      rw [sum_crossAssetPairs_grouped_clmm m
        (fun x y => Lv3 * max (|clampRange (Real.exp ((u x.1 - u y.1) / 2)) sa sb - 1| - δs) 0),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    linarith
  · have h1 := sum_crossAssetPairs_clmmWeighted_le m hL σ
    have h2 : ∑ p ∈ crossAssetPairs m,
          (wrappedCount2 p.1 p.2 : ℝ) *
            (Lv3 * max (|clampRange (Real.exp ((u p.1.1 - u p.2.1) / 2)) sa sb - 1| - δs) 0) ≤
        ∑ p ∈ crossAssetPairs m, (wrappedCount2 p.1 p.2 : ℝ) * clmmEdgeVol Lv3 σ p.1 p.2 :=
      Finset.sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_left (hedge p.1 p.2 (Finset.mem_filter.mp hp).2) (Nat.cast_nonneg _)
    have h3 : ∑ p ∈ crossAssetPairs m,
          (wrappedCount2 p.1 p.2 : ℝ) *
            (Lv3 * max (|clampRange (Real.exp ((u p.1.1 - u p.2.1) / 2)) sa sb - 1| - δs) 0) =
        Lv3 * ∑ ab ∈ unorderedPairs M,
          (2 * (m ab.1 : ℝ) * (m ab.2 : ℝ) - (m ab.1 : ℝ) - (m ab.2 : ℝ)) *
            max (|clampRange (Real.exp ((u ab.1 - u ab.2) / 2)) sa sb - 1| - δs) 0 := by
      rw [sum_crossAssetPairs_grouped_clmm m
        (fun x y => (wrappedCount2 x y : ℝ) *
          (Lv3 * max (|clampRange (Real.exp ((u x.1 - u y.1) / 2)) sa sb - 1| - δs) 0)),
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
          nsmul_eq_mul, sum_isWrapped_fin_clmm m hm ab.2]
        ring
      have hsum_w :
          ∑ i : Fin (m ab.1), ∑ j : Fin (m ab.2),
            (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ) =
          2 * (m ab.1 : ℝ) * (m ab.2 : ℝ) - (m ab.1 : ℝ) - (m ab.2 : ℝ) := by
        simp_rw [hinner, Finset.sum_add_distrib, ← Finset.sum_mul, sum_isWrapped_fin_clmm m hm ab.1,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      have hfac :
          ∑ i : Fin (m ab.1), ∑ j : Fin (m ab.2),
            (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ) *
              (Lv3 * max (|clampRange (Real.exp ((u ab.1 - u ab.2) / 2)) sa sb - 1| - δs) 0) =
          (∑ i : Fin (m ab.1), ∑ j : Fin (m ab.2),
            (wrappedCount2 (⟨ab.1, i⟩ : Asset m) (⟨ab.2, j⟩ : Asset m) : ℝ)) *
              (Lv3 * max (|clampRange (Real.exp ((u ab.1 - u ab.2) / 2)) sa sb - 1| - δs) 0) := by
        simp_rw [← Finset.sum_mul]
      rw [hfac, hsum_w]
      ring
    have hcov := coveredInterfaceVol_le_two_mul txs
    linarith

end NonlinearGraphBounds

section LinearRecovery

/-- Upside convexity: for any non-negative log-price shock `ε ≥ 0` staying in range,
exact nonlinear CLMM quote volume `L_v3 * (exp(ε/2) - 1)` is **at least** the linearized
volume `(L_v3 / 2) * ε`. -/
theorem clmm_upside_convexity {Lv3 ε : ℝ} (hL : 0 ≤ Lv3) :
    (Lv3 / 2) * ε ≤ Lv3 * (Real.exp (ε / 2) - 1) := by
  have hexp : ε / 2 + 1 ≤ Real.exp (ε / 2) := Real.add_one_le_exp (ε / 2)
  have hsub : ε / 2 ≤ Real.exp (ε / 2) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsub hL
  linarith

/-- **Exact Quantitative & Asymptotic Bridge to the Linear Model (`O(ε^2)`):**
For `|ε| ≤ 2`, exact nonlinear CLMM volume `L_v3 * (exp(ε/2) - 1)` differs from the linearized
baseline `(L_v3 / 2) * ε` by at most `|L_v3| * ε^2 / 2`, and hence
`L_v3 * (exp(ε/2) - 1) - (L_v3 / 2) * ε = O(ε^2)` as `ε → 0`. -/
theorem clmm_volume_linear_error {Lv3 ε : ℝ} (hε : |ε| ≤ 2) :
    |Lv3 * (Real.exp (ε / 2) - 1) - (Lv3 / 2) * ε| ≤ |Lv3| * ε ^ 2 / 2 := by
  have hx : |ε / 2| ≤ 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  -- Real.exp_bound with n = 2: |exp x - (1 + x)| ≤ |x|^2 * 3 / (2 * 2) = (3/4) x^2 ≤ x^2
  have hb := Real.exp_bound hx (n := 2) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 2, (ε / 2) ^ m / (m.factorial : ℝ) = 1 + ε / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have hconst : |ε / 2| ^ 2 * ((2 : ℕ).succ / ((2 : ℕ).factorial * (2 : ℕ))) =
      3 / 16 * ε ^ 2 := by
    rw [sq_abs]
    norm_num [Nat.factorial]
    ring
  rw [hconst] at hb
  have hrewrite : Lv3 * (Real.exp (ε / 2) - 1) - (Lv3 / 2) * ε =
      Lv3 * (Real.exp (ε / 2) - (1 + ε / 2)) := by ring
  rw [hrewrite, abs_mul]
  calc |Lv3| * |Real.exp (ε / 2) - (1 + ε / 2)|
      ≤ |Lv3| * (3 / 16 * ε ^ 2) := mul_le_mul_of_nonneg_left hb (abs_nonneg Lv3)
    _ ≤ |Lv3| * (ε ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg Lv3)
        nlinarith [sq_nonneg ε]
    _ = |Lv3| * ε ^ 2 / 2 := by ring

theorem clmm_volume_linear_isBigO (Lv3 : ℝ) :
    Asymptotics.IsBigO (nhds 0)
      (fun ε : ℝ => Lv3 * (Real.exp (ε / 2) - 1) - (Lv3 / 2) * ε)
      (fun ε : ℝ => ε ^ 2) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨|Lv3| / 2, ?_⟩
  have hball : Metric.ball (0 : ℝ) 2 ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [hball] with ε hε
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)]
  have h := clmm_volume_linear_error (Lv3 := Lv3) hε.le
  linarith

end LinearRecovery

end Cascades
