import Cascades

/-!
# Axiom Audit

Prints the exact axioms depended upon by every headline theorem in `Cascades`.
All theorems should depend exclusively on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) with zero `sorryAx` and zero custom axioms.
-/

#print axioms Cascades.triangleProfit_eq_opt_iff
#print axioms Cascades.residualSeq_step_from_trade
#print axioms Cascades.tradeSeq_hasSum
#print axioms Cascades.targetPoolVolume_hasSum
#print axioms Cascades.origWrapperTaxable_hasSum
#print axioms Cascades.wrapperWrapperTaxable_hasSum
#print axioms Cascades.burn_firstOrder_isBigO
#print axioms Cascades.exists_threshold_stopping_round
#print axioms Cascades.burn_quantitative_sq_bound

#print axioms Cascades.card_pool_eq
#print axioms Cascades.card_pool_equal
#print axioms Cascades.cascadeSchedule_spec
#print axioms Cascades.directSchedule_taxVol
#print axioms Cascades.cascadeSchedule_doubles_direct
#print axioms Cascades.equalFamily_boxed_formulas

#print axioms Cascades.grossYield_scale_invariant
#print axioms Cascades.grossYield_eq_yieldFixedMu
#print axioms Cascades.yieldFixedMu_step_diff
#print axioms Cascades.yieldFixedMu_step_pos
#print axioms Cascades.yieldFixedMu_tendsto
#print axioms Cascades.totalShock_evenShocks
#print axioms Cascades.realizable_fixed_mean_shock
#print axioms Cascades.grossYield_fixedSpread
#print axioms Cascades.yieldFixedSpread_step_neg
#print axioms Cascades.meanPairwiseShock_evenShocks_tendsto
#print axioms Cascades.yieldFixedSpread_tendsto
#print axioms Cascades.yield_snoc_gt_iff
#print axioms Cascades.table_section3_verified
#print axioms Cascades.table_section4_verified

#print axioms Cascades.directProfit_le_opt
#print axioms Cascades.cascade_total_profit_hasSum
#print axioms Cascades.cascade_total_profit_eq_direct
#print axioms Cascades.edgeVol_ge_residual_change
#print axioms Cascades.edgeVol_ge_of_equilibrium
#print axioms Cascades.any_equilibrium_vol_ge
#print axioms Cascades.any_equilibrium_interface_ge
#print axioms Cascades.any_equilibrium_taxVol_ge_shared
#print axioms Cascades.any_equilibrium_equal_taxVol_floor
#print axioms Cascades.any_equilibrium_equal_taxVol_unshared
#print axioms Cascades.any_equilibrium_yield_ge_floor
#print axioms Cascades.yieldFloor_step_pos
#print axioms Cascades.yieldFloor_tendsto
