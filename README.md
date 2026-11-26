# Cascades — Machine-Checked Lean 4 Formalization

Complete **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formal verification of [`cascades.md`](./cascades.md) (*A funded cascade across multiple underlying-asset families*).

Every mathematical claim, inductive complete-graph schedule invariant, asymptotic limit, family-addition criterion, and numerical table entry in `cascades.md` is machine-checked by the Lean 4 kernel with **zero `sorry`s and zero custom axioms** (only Lean's standard `[propext, Classical.choice, Quot.sound]`).

---

## Theorem Map

| Paper section (`cascades.md`) | Machine-checked theorems | File |
|---|---|---|
| **Sec. 1 — Local triangle optimality & contraction** | `triangleProfit_eq_sub_sq`, `triangleProfit_le_opt`, `triangleProfit_eq_opt_iff`, `triangleProfit_opt_pos`, `residualSeq_step_from_trade`, `residualSeq_tendsto_zero`, `tradeSeq_hasSum` | [`Cascades/SingleTarget.lean`](./Cascades/SingleTarget.lean) |
| **Sec. 1–2 — Per-target pool & taxable leg sums** | `targetPoolVolume_hasSum` ($5D\varepsilon$), `origWrapperTaxable_hasSum` ($2D\varepsilon$), `wrapperWrapperTaxable_hasSum` ($4D\varepsilon$) | [`Cascades/SingleTarget.lean`](./Cascades/SingleTarget.lean) |
| **Result — Small-burn $O(f^2)$ remainder** | `burn_firstOrder_isBigO`, `exists_threshold_stopping_round`, `burn_quantitative_sq_bound` | [`Cascades/SingleTarget.lean`](./Cascades/SingleTarget.lean) |
| **Result & Sec. 5 — Complete-graph pool counts** | `card_pool_eq` ($P = N(N-1)/2$), `card_pool_equal` ($P = Mm(Mm-1)/2$) | [`Cascades/GraphSchedule.lean`](./Cascades/GraphSchedule.lean) |
| **Sec. 1, 2, 5 — Explicit 4-stage complete-graph schedule** | `cascadeSchedule_spec` (inductive support-fairness `ValidTrace`, all pools end fair `res x y = 0`, exact unequal-family $V$ & $T$), `cascadeSchedule_doubles_direct` ($T = 2 T_{\text{direct}}$), `equalFamily_boxed_formulas` | [`Cascades/GraphSchedule.lean`](./Cascades/GraphSchedule.lean) |
| **Sec. 3 — Fixed mean pairwise shock $\mu$** | `grossYield_eq_yieldFixedMu`, `yieldFixedMu_step_diff`, `yieldFixedMu_step_pos` ($Y_{M+1} > Y_M$), `yieldFixedMu_tendsto` ($Y_M \to \frac{4f\kappa n\mu}{n+1}$), `realizable_fixed_mean_shock` ($w_M < 3\mu$) | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Sec. 4 — Fixed outer spread $\varepsilon$ & literal addition** | `totalShock_evenShocks`, `grossYield_fixedSpread`, `yieldFixedSpread_step_neg` ($Y_{M+1} < Y_M$), `meanPairwiseShock_evenShocks_tendsto` ($\mu_M \to \varepsilon/3$), `yieldFixedSpread_tendsto`, `yield_snoc_gt_iff` | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Sec. 5 — Scale invariance** | `grossYield_scale_invariant` | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Sec. 3 & 4 — Numerical tables** | `table_section3_verified`, `table_section4_verified` (exact rationals + `< 0.0005` rounding check on every printed row) | [`Cascades/YieldScaling.lean`](./Cascades/YieldScaling.lean) |
| **Axiom audit** | `#print axioms` on all 29 headline theorems | [`Cascades/Verify.lean`](./Cascades/Verify.lean) |

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

Lean proves `Assumptions -> Conclusion`. Specifically, this formalization certifies the complete mathematical mechanism within the paper's local equal-depth model ($D = \kappa L$, fixed in-range CLMM liquidity, untaxed originals, exempt mint/redemption, direct pool-to-pool triangle settlement, and restored-support execution). As noted in `cascades.md`, it does **not** claim to prove that live CLMM positions never go out of range, that competing MEV searchers necessarily select this schedule over alternative routes, or that consolidated net P&L is positive once backing reserves, external price exposure, and outside arbitrage extraction are included.
