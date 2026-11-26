# Cascades — Machine-Checked Lean 4 Formalization

Complete **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formal verification of [`cascades.md`](./cascades.md) (*A funded cascade across multiple underlying-asset families*), extended across seven modules covering every structural boundary of the model:

1. **Local triangular arbitrage & small-burn expansion** (`SingleTarget.lean`),
2. **Explicit 4-stage complete-graph state machine & 2× doubling** (`GraphSchedule.lean`),
3. **Yield scaling, limits, fixed-spread reversal, literal addition & tables** (`YieldScaling.lean`),
4. **Routing-independent universal lower bounds & surplus conservation** over *all* arbitrary clearing executions (`UniversalBounds.lean`),
5. **Exact nonlinear Uniswap-v3 concentrated-liquidity CLMM mathematics** with finite ranges `[s_a, s_b]` and range-exhaustion clamping (`NonlinearCLMM.lean`),
6. **Consolidated Net P&L, LP swap fees, LVR & fixed gas activation thresholds** (`NetLedger.lean`), and
7. **Full structural dynamics**: exact all-orders nonlinear burn/NAV feedback beyond $O(f^2)$, non-exempt mint/redemption & router-intermediary taxes, separately funded backing reserves & carry costs, and the multi-period price-regime trichotomy (bounded mean-reverting vs. symmetric random walk vs. trending) (`FullDynamics.lean`).

All **79 audited headline theorems** compile with **zero `sorry`s and zero custom axioms** (exclusively Lean's standard `[propext, Classical.choice, Quot.sound]`).

---

## Theorem Map

| Module & Scope | Machine-checked theorems | File |
|---|---|---|
| **Local triangle optimality, contraction, leg sums & $O(f^2)$ burn** | `triangleProfit_eq_opt_iff`, `residualSeq_step_from_trade`, `tradeSeq_hasSum`, `targetPoolVolume_hasSum` ($5D\varepsilon$), `origWrapperTaxable_hasSum` ($2D\varepsilon$), `wrapperWrapperTaxable_hasSum` ($4D\varepsilon$), `burn_firstOrder_isBigO`, `exists_threshold_stopping_round`, `burn_quantitative_sq_bound` | [`Cascades/SingleTarget.lean`](./Cascades/SingleTarget.lean) |
| **Complete-graph pool counts, explicit 4-stage state machine & 2× doubling** | `card_pool_eq`, `card_pool_equal`, `cascadeSchedule_spec` (`ValidTrace`, all pools end fair, exact unequal-family $V$ & $T$), `directSchedule_taxVol`, `cascadeSchedule_doubles_direct`, `equalFamily_boxed_formulas` | [`Cascades/GraphSchedule.lean`](./Cascades/GraphSchedule.lean) |
| **Sec. 3–5 yield scaling, limits, realizability, addition iff & tables** | `grossYield_scale_invariant`, `grossYield_eq_yieldFixedMu`, `yieldFixedMu_step_diff`, `yieldFixedMu_step_pos`, `yieldFixedMu_tendsto`, `totalShock_evenShocks`, `realizable_fixed_mean_shock`, `grossYield_fixedSpread`, `yieldFixedSpread_step_neg`, `meanPairwiseShock_evenShocks_tendsto`, `yieldFixedSpread_tendsto`, `yield_snoc_gt_iff`, `table_section3_verified`, `table_section4_verified` | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Routing-independent universal bounds & surplus conservation** | `directProfit_le_opt`, `cascade_total_profit_hasSum`, `cascade_total_profit_eq_direct` ($D\varepsilon^2/2$), `edgeVol_ge_residual_change`, `edgeVol_ge_of_equilibrium`, `any_equilibrium_vol_ge`, `any_equilibrium_interface_ge`, `any_equilibrium_taxVol_ge_shared` (arbitrary routes/orderings/2-pool sharing & stopping hurdle $\delta \ge 0$), `any_equilibrium_equal_taxVol_floor` ($\ge \frac{1}{4} T_{\text{cascade}}$), `any_equilibrium_equal_taxVol_unshared` ($\ge \frac{1}{2} T_{\text{cascade}}$), `any_equilibrium_yield_ge_floor`, `yieldFloor_step_pos`, `yieldFloor_tendsto` | [`Cascades/UniversalBounds.lean`](./Cascades/UniversalBounds.lean) |
| **Exact nonlinear Uniswap-v3 CLMM & range exhaustion** | `clmm_const_product` ($X_{\text{virt}} Y_{\text{virt}} = \mathcal{L}^2$), `clmm_reserves_nonneg`, `clmm_boundary_exhaustion`, `clmm_symmetric_depth_multiplier` ($\kappa = \frac{1}{4(1-r^{-1})}$), `clmmArbProfit_eq_hodl_sub_pool`, `clmmArbProfit_eq_sub_sq`, `clmmArbProfit_le_clamp`, `clmm_inRange_exact_lvr`, `clmm_outOfRange_caps_lvr`, `clmm_roundTrip_hodl_vs_lvr`, `clmmEdgeVol_ge_delta`, `clmm_complete_graph_bounds`, `clmm_upside_convexity`, `clmm_volume_linear_error`, `clmm_volume_linear_isBigO` | [`Cascades/NonlinearCLMM.lean`](./Cascades/NonlinearCLMM.lean) |
| **Consolidated Net P&L, LP fees, LVR & fixed gas** | `singleShockNetPnL_pos_iff`, `burnOnly_permanent_shock_neg`, `cascade_netPnL_sub_direct`, `cascade_fee_breakEven_comparison`, `roundTrip_hodl_and_lvr`, `fixedCost_activation_threshold` | [`Cascades/NetLedger.lean`](./Cascades/NetLedger.lean) |
| **All-orders burn/NAV feedback, non-exempt taxes, backing costs & multi-period price regimes** | `nav_conservation_of_backing` ($(S_0 - B)\cdot\text{NAV} = R_0$), `nav_appreciation_exact` ($\frac{b}{1-b} = b + \frac{b^2}{1-b}$), `nav_appreciation_gt_linear`, `nav_exact_remainder_bounds` ($b^2 \le \frac{b}{1-b}-b \le 2b^2$), `nav_feedback_geometric_hasSum`, `generalized_cascade_ratio`, `generalized_ratio_special_cases` ($2\times$ exempt, $1.5\times$ equal tax, strictly in $(1, 2)$ for $f, \tau_m > 0$), `tax_choke_threshold`, `consolidated_yield_proportional_backing`, `linear_backing_dilution_vanishes`, `consolidated_net_roi_pos_iff`, `multiperiod_lvr_regime_invariant`, `meanReverting_beats_hodl_eventually`, `trending_loses_to_hodl_eventually`, `sum_sq_walkDisplacement` ($\mathbb{E}[(u_T-u_0)^2] = T\varepsilon^2$), `randomWalk_expected_netPnL_pos_iff` | [`Cascades/FullDynamics.lean`](./Cascades/FullDynamics.lean) |
| **Axiom audit** | `#print axioms` on all 79 headline theorems | [`Cascades/Verify.lean`](./Cascades/Verify.lean) |

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

## Complete Economic Picture (Machine-Checked Boundaries)

Rather than leaving structural caveats informal, the repository formally proves **exact necessary and sufficient thresholds** across every regime:

1. **Zero asset creation from thin air (`nav_conservation_of_backing`):** Burning wrapper supply $B_{\text{sh}}$ raises per-share NAV super-linearly by $\frac{b}{1-b} > b$, while total backing claim $(S_0 - B_{\text{sh}})\cdot \text{NAV} = R_0$ is strictly conserved—burns redistribute backing claims, not new external assets.
2. **Routing independence & exact nonlinear CLMMs (`UniversalBounds.lean`, `NonlinearCLMM.lean`):** Even with arbitrary rational routing, maximal 2-pool transfer sharing, gas hurdles $\delta \ge 0$, and exact Uniswap-v3 range clamping $[s_a, s_b]$, every clearing execution satisfies strict volume/transfer lower bounds and (in-range) a strictly increasing gross-yield floor.
3. **Non-exempt taxes & backing dilution (`FullDynamics.lean`):** Non-exempt mint/redemption tax $\tau_m > 0$ moves the cascade-to-direct ratio continuously from $2\times$ ($\tau_m = 0$) into $(1, 2)$ and creates exact activation hurdles (`tax_choke_threshold`). Proportional backing $K_{\text{back}} = \lambda_b K_{\text{pool}}$ dilutes yield by $\frac{1}{1+\lambda_b}$ (whereas $O(M)$ linear backing dilution vanishes as $M \to \infty$), and carry rate $r_c$ enters consolidated net ROI additively alongside LVR (`consolidated_net_roi_pos_iff`).
4. **Price-regime trichotomy (`NetLedger.lean`, `FullDynamics.lean`):**
   * **Against dynamic rebalancing (LVR):** $T$-step net P&L has the exact same break-even $\varepsilon < \frac{2 c_{\text{rev}}}{m^2}$ for all $T \ge 1$ regardless of whether prices mean-revert or trend (`multiperiod_lvr_regime_invariant`); burn alone ($\phi = 0$) loses to permanent-shock LVR whenever $|u_a - u_b| > 8f$ (`burnOnly_permanent_shock_neg`).
   * **Against HODL (IL):** Bounded mean-reverting paths (`|u_T - u_0| ≤ B`) **always** beat HODL for $T > \frac{m^2 B^2}{2 c_{\text{rev}} \varepsilon}$; monotone trending paths **always** lose to HODL for $T > \frac{2 c_{\text{rev}}}{m^2 \varepsilon}$; fair symmetric random walks satisfy $\mathbb{E}[(u_T-u_0)^2] = T\varepsilon^2$ and beat HODL in expectation iff $\varepsilon < \frac{2 c_{\text{rev}}}{m^2}$.
   * **What remains empirical:** Which market-regime parameters ($\varepsilon, B, \phi, \tau_m, r_c$, range widths, and actual price processes) obtain on a given live on-chain deployment.
