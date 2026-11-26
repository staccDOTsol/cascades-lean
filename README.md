# Cascades — Machine-Checked Lean 4 Formalization

Complete **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formal verification of [`cascades.md`](./cascades.md) (*A funded cascade across multiple underlying-asset families*), extended to:
1. **Routing-independent universal lower bounds** over *all* arbitrary no-arbitrage clearing executions (`UniversalBounds.lean`),
2. **Exact nonlinear Uniswap-v3 concentrated-liquidity CLMM mathematics** with finite price ranges `[s_a, s_b]` and range-exhaustion clamping (`NonlinearCLMM.lean`), and
3. **Consolidated Net P&L, LP swap-fee, and LVR break-even analysis** across single permanent shocks, full mean-reverting round-trip cycles, and fixed gas activation thresholds (`NetLedger.lean`).

All **63 audited headline theorems** compile with **zero `sorry`s and zero custom axioms** (exclusively Lean's standard `[propext, Classical.choice, Quot.sound]`).

---

## Theorem Map

| Section / Result | Machine-checked theorems | File |
|---|---|---|
| **Sec. 1 — Local triangle optimality & contraction** | `triangleProfit_eq_sub_sq`, `triangleProfit_le_opt`, `triangleProfit_eq_opt_iff`, `triangleProfit_opt_pos`, `residualSeq_step_from_trade`, `residualSeq_tendsto_zero`, `tradeSeq_hasSum` | [`Cascades/SingleTarget.lean`](./Cascades/SingleTarget.lean) |
| **Sec. 1–2 — Per-target pool & taxable leg sums** | `targetPoolVolume_hasSum` ($5D\varepsilon$), `origWrapperTaxable_hasSum` ($2D\varepsilon$), `wrapperWrapperTaxable_hasSum` ($4D\varepsilon$) | [`Cascades/SingleTarget.lean`](./Cascades/SingleTarget.lean) |
| **Result — Small-burn $O(f^2)$ remainder** | `burn_firstOrder_isBigO`, `exists_threshold_stopping_round`, `burn_quantitative_sq_bound` | [`Cascades/SingleTarget.lean`](./Cascades/SingleTarget.lean) |
| **Result & Sec. 5 — Complete-graph pool counts** | `card_pool_eq` ($P = N(N-1)/2$), `card_pool_equal` ($P = Mm(Mm-1)/2$) | [`Cascades/GraphSchedule.lean`](./Cascades/GraphSchedule.lean) |
| **Sec. 1, 2, 5 — Explicit 4-stage complete-graph schedule** | `cascadeSchedule_spec` (inductive support-fairness `ValidTrace`, all pools end fair `res x y = 0`, exact unequal-family $V$ & $T$), `cascadeSchedule_doubles_direct` ($T = 2 T_{\text{direct}}$), `equalFamily_boxed_formulas` | [`Cascades/GraphSchedule.lean`](./Cascades/GraphSchedule.lean) |
| **Sec. 3 — Fixed mean pairwise shock $\mu$** | `grossYield_eq_yieldFixedMu`, `yieldFixedMu_step_diff`, `yieldFixedMu_step_pos` ($Y_{M+1} > Y_M$), `yieldFixedMu_tendsto` ($Y_M \to \frac{4f\kappa n\mu}{n+1}$), `realizable_fixed_mean_shock` ($w_M < 3\mu$) | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Sec. 4 — Fixed outer spread $\varepsilon$ & literal addition** | `totalShock_evenShocks`, `grossYield_fixedSpread`, `yieldFixedSpread_step_neg` ($Y_{M+1} < Y_M$), `meanPairwiseShock_evenShocks_tendsto` ($\mu_M \to \varepsilon/3$), `yieldFixedSpread_tendsto`, `yield_snoc_gt_iff` | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Sec. 5 — Scale invariance & numerical tables** | `grossYield_scale_invariant`, `table_section3_verified`, `table_section4_verified` (exact rationals + `< 0.0005` rounding check on every printed row) | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Routing-independent universal bounds & surplus conservation** | `directProfit_le_opt`, `cascade_total_profit_hasSum`, `cascade_total_profit_eq_direct` (total arb surplus $= D\varepsilon^2/2$), `any_equilibrium_vol_ge`, `any_equilibrium_interface_ge`, `any_equilibrium_taxVol_ge_shared` (holds for **any** route/ordering/transfer-sharing and stopping hurdle $\delta \ge 0$), `any_equilibrium_equal_taxVol_floor` ($\ge \frac{1}{4} T_{\text{cascade}}$), `any_equilibrium_equal_taxVol_unshared` ($\ge \frac{1}{2} T_{\text{cascade}}$), `any_equilibrium_yield_ge_floor`, `yieldFloor_step_pos`, `yieldFloor_tendsto` | [`Cascades/UniversalBounds.lean`](./Cascades/UniversalBounds.lean) |
| **Exact nonlinear Uniswap-v3 CLMM & range exhaustion** | `clmm_const_product` ($X_{\text{virt}} Y_{\text{virt}} = \mathcal{L}^2$), `clmm_reserves_nonneg`, `clmm_boundary_exhaustion`, `clmm_symmetric_depth_multiplier` ($\kappa = \frac{1}{4(1-r^{-1})}$), `clmmArbProfit_eq_hodl_sub_pool`, `clmmArbProfit_eq_sub_sq`, `clmmArbProfit_le_clamp` (unique clamped optimum), `clmm_inRange_exact_lvr`, `clmm_outOfRange_caps_lvr`, `clmm_roundTrip_hodl_vs_lvr`, `clmmEdgeVol_ge_delta`, `clmm_complete_graph_bounds` (routing-independent nonlinear bounds with range clamping), `clmm_upside_convexity`, `clmm_volume_linear_error`, `clmm_volume_linear_isBigO` ($O(\varepsilon^2)$ recovery of linear model) | [`Cascades/NonlinearCLMM.lean`](./Cascades/NonlinearCLMM.lean) |
| **Consolidated Net P&L, LP fees & LVR ledger** | `singleShockNetPnL_pos_iff` (exact iff break-even: $Q_M / S_M < 2(\frac{\alpha n}{n+1} f + \frac{\beta}{(n+1)^2}\phi)$), `burnOnly_permanent_shock_neg` (burn alone is strictly net-negative against permanent LVR when $|u_a - u_b| > 8f$), `cascade_netPnL_sub_direct`, `cascade_fee_breakEven_comparison` (cascade lifts fee break-even from $2\phi$ to $2(5 - 4/(n+1)^2)\phi$), `roundTrip_hodl_and_lvr` (round-trip $> 0$ vs. HODL; exact break-even vs. dynamic-rebalancing LVR), `fixedCost_activation_threshold` ($L > C_{\text{gas}} / (\kappa \gamma)$) | [`Cascades/NetLedger.lean`](./Cascades/NetLedger.lean) |
| **Axiom audit** | `#print axioms` on all 63 headline theorems | [`Cascades/Verify.lean`](./Cascades/Verify.lean) |

---

## Independent Local Verification

Requires [`elan`](https://github.com/leanprover/elan) (Lean's toolchain manager).

```bash
git clone https://github.com/staccDOTsol/cascades-lean.git
cd cascades-lean
lake exe cache get
lake build
lake env lean Cascades/Verify.lean
```

Every theorem in `Cascades/Verify.lean` prints:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## What Is Proved — and Where the Economics Lands

Lean checks `Assumptions -> Conclusion`. Putting all six modules together gives a completely transparent picture:

1. **Routing independence (`UniversalBounds.lean`):** Even if rational searchers ignore the 4-stage cascade, pick arbitrary routes/orderings, maximize 2-pool transfer sharing, and stop early at hurdle $\delta \ge 0$, every clearing equilibrium still generates at least $\frac{1}{4}$ of the cascade's taxable volume ($\frac{1}{2}$ unshared) and still exhibits a strictly increasing gross-burn yield floor $Y_{\text{floor}}(M) = f\kappa n\mu\frac{M-1}{M(n+1)-1} \to \frac{f\kappa n\mu}{n+1}$.
2. **Exact nonlinear CLMMs & range limits (`NonlinearCLMM.lean`):** The linear `-q / D` model is rigorously justified at $O(\varepsilon^2)$ from exact Uniswap-v3 virtual reserves $X_{\text{virt}} Y_{\text{virt}} = \mathcal{L}^2$ with $\kappa = \frac{1}{4(1-r^{-1})}$, and the routing-independent volume/transfer lower bounds hold *non-linearly* with exact range clamping `clamp(exp((u_a - u_b)/2), s_a, s_b)`. Range exhaustion strictly caps both LVR and arbitrage volume.
3. **Consolidated Net P&L honesty (`NetLedger.lean`):**
   * On a **permanent one-way shock** with zero LP swap fees ($\phi = 0$), proportional burn alone ($f \ll \varepsilon$) is **provably net-negative** (`burnOnly_permanent_shock_neg`) because arbitrage extraction / LVR scales as $O(\varepsilon^2)$ while burn scales as $O(f\varepsilon)$.
   * With **LP swap fees $\phi > 0$**, net single-shock P&L (and round-trip P&L vs. dynamic rebalancing) is strictly positive **iff** $Q_M / S_M < 2\left(\frac{\alpha n}{n+1} f + \frac{\beta}{(n+1)^2}\phi\right)$—and the 4-stage cascade lifts the swap-fee break-even threshold from $2\phi$ (direct) to $2\left(5 - \frac{4}{(n+1)^2}\right)\phi$ while keeping LVR unchanged.
   * On a **full mean-reverting round-trip cycle ($0 \to u \to 0$)** measured against holding initial inventory (**HODL**), exact nonlinear CLMM IL returns to $0$ (`clmm_roundTrip_hodl_vs_lvr`), leaving net round-trip gain $2(B + F) > 0$.
   * **Outside the formal model:** nonlinear burn/NAV feedback beyond $O(f^2)$, non-exempt redemption/router taxes, funding/borrow costs of backing reserves, and whether live market prices mean-revert or trend permanently remain empirical on-chain questions.
