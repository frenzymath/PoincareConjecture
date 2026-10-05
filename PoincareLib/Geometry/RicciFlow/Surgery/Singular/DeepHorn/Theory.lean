import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.HeightSelection.UniformHeight
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.ScaleSelection.Downward

/-!
# M32 strong-neck and deep-horn proof entry

The numbered theorem assembles the source-specific deep-horn selection proof.
The provider package is explicit so later proof work can use the reviewed M04,
M19, M25, M29, and M30 services, together with the M31 singular-limit theory
supplied at selection time. The selected M29 and M30 thresholds supply the
universal small-epsilon witness before any flow, limit, or horn is chosen.
`Proofs/M32/Providers.lean` supplies these services by actual theorem
applications; callers need not reconstruct their predecessor packages.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Morgan--Tian Theorem 11.31 (printed pp. 287--292): with fixed geometric and
analytic constants and `0 < rho < r0`, first select a threshold below half
the actual M29 and M30 thresholds, then for every `delta > 0` choose a positive
`h <= min (rho * delta) (rho / (2 C))` before quantifying any generalized flow.
For every flow satisfying the reviewed regular-time extension of Assumptions 11.18,
every singular-limit conclusion,
and every strong `2 epsilon`-horn whose boundary lies in Omega_{rho/(2 C)},
each point with terminal scalar at least `h⁻²` is the center of a strong
`delta`-neck contained in that horn. A selected point has scalar `h⁻²`, and its
central sphere cuts off an end disjoint from Omega_rho. The proof invokes
Theorem 11.1, its Theorem 10.2 bounded-distance input, Corollary 9.50, and
Appendix A.21/A.25; their reviewed services are the M29, M30, M19, and M25
providers. M04 scalar evolution and the actual spatial neck jets supply the
strict positive time-derivative margin in Claim 11.35. An absolute derivative
bound alone does not give that sign. M31 supplies the terminal extension.
Corollary 11.36 also supplies a monotone two-variable height function with
the same geometric conclusion at every smaller positive height. Apply the
theorem after reducing the canonical radius to rho and its cutoff to rho/2;
this retains the supplied terminal extension and removes dependence on the
original radius. The dyadic construction uses the least eligible index,
correcting `MT-11.36-SELECTOR-INDEX`. See the derivation in
`reviews/contracts/2026-09-15-uniform-surgery-calibration.md`.
The selector fixes the analytic coefficient before quantifying flows;
that coefficient supplies M30's guarded analytic bounds on the terminal
extension. Keep the separate `terminalAccuracyFactor * epsilon <= A.epsilon0`
premise for the
later arbitrary Appendix-A theory A; the universal threshold precedes A.
`reviews/contracts/2026-09-15-analytic-selector-round1.md` records why this
dependence preserves the geometric boundary radius and the same limit.
The one-sided endpoint and incomplete-limit conventions follow
`reviews/errata/2026-09-10-source-audit.md`.
The complete derivation and internal supporting obligations are in
`reviews/contracts/2026-09-17-m32-full-contract.md`. The regular-time boundary
review dated 2026-09-18 applies M29/M30 to the supplied terminal extension
using original preterminal (C, epsilon) certificates at left-dense times.
Terminal horns at the universal accuracy factor (see `terminalAccuracyFactor`)
supply its separate volume/worldline buffers.
In Claim 11.35, continuity extends the regular-time scalar monotonicity to
exceptional times before the actual neck cylinders extend a compact region.
-/
/-- Strong necks, exact deep-horn cuts and a common monotone scale selector.
Source: Morgan--Tian Theorem 11.31, pp. 287-292, and Corollary 11.36, p. 292. -/
theorem m32HornSelection
    (P : RepairedHornSelectionPredecessors.{u}) :
    RepairedHornSelectionTheory.{u} := by
  obtain ⟨epsilonDeep, hDeepPos, hDeepSmall, hdeep⟩ := M32.exists_uniform_deepHornHeight P
  obtain ⟨tauDownward, hDownPos, _hDownSmall, hselector⟩ :=
    M32.exists_deepHornScaleSelection_of_pointwiseHeight.{u}
  refine {
    providers := P
    deep_horn := ⟨epsilonDeep, hDeepPos, hDeepSmall, ?_⟩
    scale_selection := ?_
    selection := ?_ }
  · intro epsilon hepsilon hsmall r₀ C analyticConstant rho delta
      hr₀ hC hAnalytic hrho hrhor₀ hdelta A hA
    obtain ⟨h, hh, hheight⟩ := hdeep epsilon hepsilon hsmall
      r₀ C analyticConstant rho delta hr₀ hC hAnalytic hrho hrhor₀ hdelta A hA
    exact ⟨h, hh, hheight.1, hheight.2⟩
  · let epsilonSelector := min epsilonDeep (tauDownward / terminalAccuracyFactor)
    have hSelectorPos : 0 < epsilonSelector :=
      lt_min hDeepPos (div_pos hDownPos terminalAccuracyFactor_pos)
    refine ⟨epsilonSelector, hSelectorPos, (min_le_left _ _).trans hDeepSmall, ?_⟩
    intro epsilon C analyticConstant hepsilon hsmall hC hAnalytic A hA
    have hDeep : epsilon ≤ epsilonDeep := hsmall.trans (min_le_left _ _)
    have hDown : terminalAccuracyFactor * epsilon ≤ tauDownward :=
      (le_div_iff₀' terminalAccuracyFactor_pos).mp (hsmall.trans (min_le_right _ _))
    apply hselector epsilon C analyticConstant hDown hC
    intro r₀ rho delta hr₀ hrho hrhor₀ hdelta
    exact hdeep epsilon hepsilon hDeep r₀ C analyticConstant rho delta
      hr₀ hC hAnalytic hrho hrhor₀ hdelta A hA
  · intro L31 M _ _ _ _ _ _ _ _ F T H A hsmall _hA
    obtain ⟨Q⟩ := (Classical.choose_spec (L31.limit A)).2.2 H hsmall
    exact ⟨{ limit := Q }⟩

end PoincareMT
