# Corrections to the source

Places where a claim in Chapter 1 of Woodford (2003) is imprecise or relies on
an unstated hypothesis, and where the Lean statement departs from the printed
one. Lean names are relative to the namespace `Woodford.ReturnOfMonetaryRules`.
No claim in the chapter was found to be false.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| §4.3, pp. 50–51 | `φ > 0` gives `0 < α < 1` and hence a unique bounded solution (4.12). | Sufficient but not necessary: a unique bounded equilibrium exists for every bounded shock process iff `φ > 0` or `φ < −2` (`NeoWicksellian.existsUnique_iff`). For `φ < −2` the price level is determined but oscillates; for `−2 ≤ φ ≤ 0` there is a continuum of bounded equilibria (`NeoWicksellian.not_unique_of_mem_Icc`); under a peg (`φ = 0`) a bounded equilibrium may not exist at all (`NeoWicksellian.peg_no_bounded`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (3.1), p. 27 | `F` is a distribution function | Monotone with limits 0 and 1 (`ChannelSystem.IsCDF`); with right-continuity this is exactly the CDF of a probability measure (`ChannelSystem.isCDF_cdf`, `ChannelSystem.exists_measure_of_isCDF`) |
| (3.2), p. 28 | `F⁻¹(1/2)` exists and is unique | Continuity and strict monotonicity (`ChannelSystem.exists_eq_half`, `ChannelSystem.existsUnique_target_supply`) |
| pp. 25–31 | The reserve-demand model behind (3.1) | Not stated in the book (it cites Woodford 2001c); not formalised |
| (4.5)–(4.6), p. 41 | Convergence of the partial-adjustment rule | Schur–Cohn stability of the lag polynomial (`InterestRateRules.partialAdjustment_tendsto`) |
