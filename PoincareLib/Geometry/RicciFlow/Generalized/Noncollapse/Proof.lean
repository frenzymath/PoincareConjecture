import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Combined
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Uniform.Assembly
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.ProviderEstimate
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Assembly

/-! Adapted from Mapher `PoincareMT/Proofs/M15.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# M15 noncollapsing proof entry

This file is the sole proof owner for the corrected M15 contract.  Earlier
definitions, statements, and predecessor milestones are read-only inputs.
The helpers in `Proofs/M15/` prove generalized Theorem 8.1 and compact
Theorem 8.10 with their original quantifiers and geometric hypotheses.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareMT

/--
Morgan--Tian Theorem 8.1, Proposition 8.2 and Lemmas 8.3--8.9, printed
pp. 169--176, give a uniform `kappa * r^n` lower bound from one actual
based compatible radius-r cylinder, compact terminal-ball closure, full
curvature control, an open stable `W` in the M14 fixed-time exponential
domain, a normalized reduced-length bound, and a positive terminal image
volume.  The generalized constant is chosen from `n`, `taubar`, `l₀`, and
`V` before the flow and configuration; its provider-to-predicate clause uses
the actual M11/M12 spacetime and selected slice measure.  Morgan--Tian
Theorem 8.10, pp. 176--177, is a separate compact three-dimensional clause:
its positive constant depends only on `omega` and `T₀`, while the supplied
ordinary flow contributes the initial curvature, initial unit-ball volume,
valid-time, and tested-cylinder hypotheses.  The proof consumes the actual
M04 curvature/metric/norm-evolution services, M12 gauge and ordinary-product
services, M13 exact rescaling, and M14 variational and measure outputs in
both dimension n and dimension three. M08/M09/M10 ordinary services are an
explicit dimension-three input to M14's captured ordinary branch; M14 does
not produce them. Proposition 7.5 and Theorem 7.10 (pp. 151--155) supply
the full-measure locus and low reduced-length point used in Theorem 8.10.
The Chapter 8 qualifications in
`reviews/contracts/M15-repair-contract.md` correct the small-domain gradient
and volume comparisons, the Gaussian tail estimate, and half-open endpoint
handling; the tensor-evolution and reduced-length corrections are recorded
in `reviews/errata/2026-09-11-tensor-evolution.md` and
`reviews/errata/2026-09-13-reduced-length-source.md`.  No legacy fixed-carrier
noncollapsing theorem or desired-volume inequality is a predecessor.
The corrected dependency boundary is recorded in
`reviews/contracts/2026-09-15-m14-m15-correction-round1.md`.
-/
theorem noncollapsingGeneralizedAndCompact
    (n : ℕ)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hM12 : ∀ d : ℕ, GeneralizedRicciGaugeTheory.{u} d)
    (hM13 : ∀ d : ℕ, GeneralizedParabolicRescalingTheory.{u} d)
    (hM14 : ∀ d : ℕ, GeneralizedLGeometryTheory.{u} d)
    (hOrdinary : M14OrdinaryProviders.{u} 3) :
    NoncollapsingConclusion.{u} n := by
  refine {
    generalized := {
      uniform := Generalized.Noncollapse.generalizedUniformTheorem hM04 n (hM12 n) (hM13 n) (hM14 n)
      provider_bridge := ?_
    }
    compact := ⟨Generalized.Noncollapse.compactTheorem810 hM04 (hM12 3) (hM13 3) (hM14 3) hOrdinary⟩
  }
  intro X _ time I G Omega taubar l0 V r0 U
  exact Generalized.Noncollapse.provider_implies_noncollapse G Omega taubar l0 V r0 U

end PoincareMT
