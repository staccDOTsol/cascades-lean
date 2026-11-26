# Cascades — Machine-Checked Lean 4 Formalization

Complete **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formal verification of [`cascades.md`](./cascades.md) (*A funded cascade across multiple underlying-asset families*), **plus** routing-independent lower bounds over *all* arbitrary no-arbitrage clearing executions.

Every mathematical claim, inductive complete-graph schedule invariant, universal routing-independent equilibrium floor, asymptotic limit, family-addition criterion, and numerical table entry is machine-checked by the Lean 4 kernel with **42 audited headline theorems, zero `sorry`s, and zero custom axioms** (only Lean's standard `[propext, Classical.choice, Quot.sound]`).

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
| **Routing-independent universal bounds & surplus conservation** | `cascade_total_profit_hasSum`, `cascade_total_profit_eq_direct` (total arb surplus $= D\varepsilon^2/2$), `any_equilibrium_vol_ge`, `any_equilibrium_interface_ge`, `any_equilibrium_taxVol_ge_shared` (holds for **any** route/ordering/transfer-sharing and stopping hurdle $\delta \ge 0$), `any_equilibrium_equal_taxVol_floor` ($\ge \frac{1}{4} T_{\text{cascade}}$), `any_equilibrium_equal_taxVol_unshared` ($\ge \frac{1}{2} T_{\text{cascade}}$), `any_equilibrium_yield_ge_floor`, `yieldFloor_step_pos` (strictly increasing in $M$), `yieldFloor_tendsto` ($\to \frac{f\kappa n\mu}{n+1}$) | [`Cascades/UniversalBounds.lean`](./Cascades/UniversalBounds.lean) |
| **Axiom audit** | `#print axioms` on all 42 headline theorems | [`Cascades/Verify.lean`](./Cascades/Verify.lean) |

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

## Scope & Modeling Boundary

Lean proves `Assumptions -> Conclusion`.

* **What *is* proved even without assuming a specific routing schedule (`Cascades/UniversalBounds.lean`):** Within the local equal-depth model ($D = \kappa L$, fixed in-range CLMM liquidity, untaxed originals, exempt mint/redemption), **every** arbitrage-clearing execution trace $\sigma$—regardless of whether rational searchers take direct trades, partial triangles, arbitrary orderings, or maximal pool-to-pool transfer sharing—must generate at least $\frac{1}{4}$ of the cascade's taxable volume ($\frac{1}{2}$ without cross-pool sharing), and even that worst-case routing-independent floor $Y_{\text{floor}}(M) = f\kappa n\mu \frac{M-1}{M(n+1)-1}$ is strictly increasing in family count $M$ and converges to $\frac{f\kappa n\mu}{n+1} > 0$. With any rational gas/burn stopping hurdle $\delta \ge 0$, the exact lower bound holds with $\max(|u_a - u_b| - \delta, 0)$.
* **What is *not* claimed or proved:** As noted in `cascades.md`, this formalization does **not** prove that live CLMM positions never leave their ranges, that nonlinear burn/NAV feedback vanishes beyond $O(f^2)$, or that consolidated **net P&L** is positive once backing reserves, external price exposure, and LP loss-versus-rebalancing (arb surplus $= \frac{D}{2}\varepsilon^2$ per pool) are accounted for.
