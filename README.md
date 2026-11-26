# Cascades — Machine-Checked Lean 4 Formalization

Complete **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formal verification of [`cascades.md`](./cascades.md) (*A funded cascade across multiple underlying-asset families*), extended across eight modules covering every structural boundary of the model:

1. **Local triangular arbitrage & small-burn expansion** (`SingleTarget.lean`),
2. **Explicit 4-stage complete-graph state machine & 2× doubling** (`GraphSchedule.lean`),
3. **Yield scaling, limits, fixed-spread reversal, literal addition & tables** (`YieldScaling.lean`),
4. **Routing-independent universal lower bounds & surplus conservation** over *all* arbitrary clearing executions (`UniversalBounds.lean`),
5. **Exact nonlinear Uniswap-v3 concentrated-liquidity CLMM mathematics** with finite ranges `[s_a, s_b]` and range-exhaustion clamping (`NonlinearCLMM.lean`),
6. **Consolidated Net P&L, LP swap fees, LVR & fixed gas activation thresholds** (`NetLedger.lean`),
7. **Full structural dynamics**: exact all-orders nonlinear burn/NAV feedback beyond $O(f^2)$, non-exempt mint/redemption & router-intermediary taxes, separately funded backing reserves & carry costs, and the multi-period price-regime trichotomy (bounded mean-reverting vs. symmetric random walk vs. trending) (`FullDynamics.lean`), and
8. **Compounding, sovereign wealth-share scaling & finite-market saturation**: Archimedean compounding (`n -> n++`) past any finite target under bounded positive yield, harmonic effective depth $D_{\text{eff}} = \frac{D D_{\text{ext}}}{D + D_{\text{ext}}}$, sovereign wealth-share optimization (`s(1-s)W` uniquely maximized at `s = 1/2`, with exact `1/10` vs. `1/2` yield retention), and closed-system zero-sum conservation (`CompoundingAndLimits.lean`).

All **92 audited headline theorems** compile with **zero `sorry`s and zero custom axioms** (exclusively Lean's standard `[propext, Classical.choice, Quot.sound]`).

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
| **All-orders burn/NAV feedback, non-exempt taxes, backing costs & multi-period price regimes** | `nav_conservation_of_backing`, `nav_appreciation_exact`, `nav_appreciation_gt_linear`, `nav_exact_remainder_bounds`, `nav_feedback_geometric_hasSum`, `generalized_cascade_ratio`, `generalized_ratio_special_cases`, `tax_choke_threshold`, `consolidated_yield_proportional_backing`, `linear_backing_dilution_vanishes`, `consolidated_net_roi_pos_iff`, `multiperiod_lvr_regime_invariant`, `meanReverting_beats_hodl_eventually`, `trending_loses_to_hodl_eventually`, `sum_sq_walkDisplacement`, `randomWalk_expected_netPnL_pos_iff` | [`Cascades/FullDynamics.lean`](./Cascades/FullDynamics.lean) |
| **Compounding, sovereign wealth share & finite-market saturation** | `one_add_pow_ge_linear`, `compounding_tendsto_atTop`, `compounding_exceeds_any_finite_target`, `bounded_yield_still_unbounded_compounding`, `finiteExtArbProfit_le_opt`, `effectiveDepth_lt_both`, `effectiveDepth_saturates_at_ext`, `saturated_yield_tendsto_zero`, `sovereign_share_effectiveDepth` ($D_{\text{eff}} = s(1-s)W$, yield retention $= 1-s$), `sovereign_share_max_at_half` (unique global maximum at $s = 1/2$), `sovereign_tenth_vs_half` ($1/10 \to 90\%$ yield, $1/2 \to 50\%$ yield & $25/9\times$ max absolute burn), `closed_system_zero_sum`, `no_strictly_positive_closed_system` | [`Cascades/CompoundingAndLimits.lean`](./Cascades/CompoundingAndLimits.lean) |
| **Axiom audit** | `#print axioms` on all 92 headline theorems | [`Cascades/Verify.lean`](./Cascades/Verify.lean) |

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

1. **Zero asset creation from thin air (`nav_conservation_of_backing`, `closed_system_zero_sum`):** Burning wrapper supply raises per-share NAV super-linearly by $\frac{b}{1-b} > b$ while conserving total backing reserve $(S_0 - B_{\text{sh}})\cdot\text{NAV} = R_0$; in any closed resource-conserving population, any coalition's gain equals the rest of the system's exact outflow.
2. **Compounding vs. Sovereign-Scale Saturation (`CompoundingAndLimits.lean`):**
   * Bounded per-cycle net yield $y > 0$ *does* compound past every finite target $H > 0$ (`bounded_yield_still_unbounded_compounding`) **while** internal liquidity is small relative to external markets ($D \ll D_{\text{ext}}$).
   * At **sovereign scale**—allocating share $s \in (0, 1)$ of total global liquidity $W$ into internal pools and leaving $(1-s)W$ external—exact harmonic depth is $D_{\text{eff}} = s(1-s)W$ with yield retention $1 - s$. Absolute turnover/burn peaks uniquely at **$s = 1/2$** ($\frac{1}{4}W$, $50\%$ yield retention; vs. $s = 1/10 \implies \frac{9}{100}W$, $90\%$ yield retention), and collapses back to $0$ as $s \to 1$.
3. **Routing independence, exact nonlinear CLMMs & taxes (`UniversalBounds.lean`, `NonlinearCLMM.lean`, `FullDynamics.lean`):** Routing-independent volume/transfer lower bounds hold both linearly and on exact Uniswap-v3 CLMMs with range clamping `[s_a, s_b]`, non-exempt mint/redemption taxes $\tau_m$, and router hops $k_r$.
4. **Price-regime trichotomy (`NetLedger.lean`, `FullDynamics.lean`):** Against dynamic-rebalancing LVR, the break-even $\varepsilon < \frac{2c_{\text{rev}}}{m^2}$ is regime-invariant for all $T \ge 1$ (and burn alone loses to permanent-shock LVR when $|u_a-u_b| > 8f$). Against HODL, bounded mean-reverting paths always beat HODL eventually, trending paths always lose eventually, and symmetric random walks satisfy $\mathbb{E}[(u_T-u_0)^2] = T\varepsilon^2$.
5. **What remains empirical:** Which concrete market parameters ($\varepsilon, B, \phi, \tau_m, r_c, s, W$, range widths, and realized price processes) obtain on a given live deployment.
