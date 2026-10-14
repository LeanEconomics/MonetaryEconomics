# Source map

Woodford (2003), *Interest and Prices*, Chapter 1, "The Return of Monetary Rules" (pp. 1–60).
Each formal claim is listed with its Lean name, relative to the namespace
`Woodford.ReturnOfMonetaryRules`. Page numbers are book pages.

| Book | Claim | Lean |
| --- | --- | --- |
| Woodford (3.1), p. 27 | channel-system overnight rate | `ChannelSystem.rate` |
| Woodford p. 27 | F is a CDF (Mathlib cdf link, both directions) | `ChannelSystem.IsCDF`, `ChannelSystem.isCDF_cdf`, `ChannelSystem.exists_measure_of_isCDF` |
| Woodford p. 28 | i^d ≤ i ≤ i^l | `ChannelSystem.rate_mem_channel`, `ChannelSystem.cdf_rate_mem_channel` |
| Woodford p. 28 | i decreasing in S | `ChannelSystem.rate_antitone`, `ChannelSystem.rate_strictAnti`, `ChannelSystem.cdf_rate_antitone` |
| Woodford (3.2), p. 28 | S = −F⁻¹(1/2)σ hits the target; exists and is unique | `ChannelSystem.rate_eq_target_iff`, `ChannelSystem.exists_eq_half`, `ChannelSystem.target_supply_iff`, `ChannelSystem.existsUnique_target_supply` |
| Woodford p. 28 | target supply independent of ī; symmetric case | `ChannelSystem.target_supply_set_indep`, `ChannelSystem.target_supply_symmetric` |
| Woodford p. 28 | the rate is moved by shifting the facility rates | `ChannelSystem.rate_shift_channel` |
| Woodford p. 32 | no clearing demand ⇒ i = i^d for S > 0 | `ChannelSystem.rate_noClearing`, `ChannelSystem.rate_noClearing_indep` |
| Woodford (4.1)–(4.2), fn. 30, p. 38 | difference rule ⇔ Wicksell rule | `InterestRateRules.difference_iff_wicksell`, `InterestRateRules.wicksell_intercept_eq`, `InterestRateRules.wicksell_imp_difference` |
| Woodford fn. 29, p. 38 | (4.1) incompatible with i ≥ 0 at all price levels | `InterestRateRules.wicksell_violates_zlb` |
| Woodford (4.3), p. 39 | Taylor rule: 4% at target, real rate 2% | `InterestRateRules.taylorRule_at_target`, `InterestRateRules.taylorRule_real_rate_at_target` |
| Woodford p. 40 | the Taylor principle | `InterestRateRules.taylorPrinciple_iff`, `InterestRateRules.taylorRule_real_rate_rises` |
| Woodford (4.4), p. 40 | reaction function; Goodhart rule | `InterestRateRules.reactionFn`, `InterestRateRules.goodhartRule_eq_reactionFn` |
| Table 1.1, p. 41 | coefficient comparisons; Judd–Rudebusch stability | `InterestRateRules.table11_taylor_principle`, `InterestRateRules.judd_rudebusch_stable` |
| Woodford (4.5)–(4.6), p. 41 | partial adjustment; long-run responses | `InterestRateRules.partialAdjustment_tendsto`, `InterestRateRules.partialAdjustment_longRun`, `InterestRateRules.partialAdjustment_const_iff` |
| Woodford (4.7), p. 42 | forecast-based desired rate | `InterestRateRules.ForecastDesiredRate` |
| Woodford (4.8), p. 44 | Svensson's target criterion | `InterestRateRules.TargetCriterion`, `InterestRateRules.targetCriterion_perfectForesight`, `InterestRateRules.targetCriterion_tradeoff` |
| Woodford (4.9)–(4.11), pp. 50–51 | substitution gives (4.11), α ∈ (0,1) | `NeoWicksellian.equilibrium_iff_reduced`, `NeoWicksellian.alpha_mem` |
| Woodford (4.12), p. 51 | the unique bounded solution | `NeoWicksellian.priceLevel_equilibrium`, `NeoWicksellian.eq_priceLevel`, `NeoWicksellian.existsUnique_priceLevel` |
| Woodford p. 51 | p̄ = φ⁻¹(r̄ − ī); bounded interval around p̄ | `NeoWicksellian.priceLevel_const`, `NeoWicksellian.longRun_equilibrium`, `NeoWicksellian.abs_sub_longRun_le`, `NeoWicksellian.tendsto_longRun` |
| Woodford p. 51 | p rises with r, falls with ī; news effect | `NeoWicksellian.equilibrium_mono`, `NeoWicksellian.weights_pos` |
| Woodford pp. 38, 51 | the role of φ > 0 | `NeoWicksellian.not_unique_of_mem_Icc`, `NeoWicksellian.peg_no_bounded`, `NeoWicksellian.existsUnique_iff` |
| Woodford (4.13), fn. 44, p. 52 | sticky prices; the Taylor principle | Forward pointer to Chapters 2 and 4; not formalised here |
| Table 1.1, pp. 41–42 | estimated reaction functions | Empirical; only the coefficient facts are formalised |
