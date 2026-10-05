import PoincareLib.Geometry.CurveShortening.Evolution.CorrectedTheory
import PoincareLib.Geometry.RicciFlow.CurveShortening.Construction
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-!
# Construction of the corrected curve-evolution theory

This module assembles the actual spacetime, product-circle, curve,
regularization, integral, and slope constructions with the pinned M62
signature. The source service hypothesis is retained unchanged.

Sources: Morgan--Tian, Lemma 19.6 and Claim 19.11, pp. 441-446; Morgan--Tian
2015 correction, (0.1)-(0.2), Lemmas 0.1-0.2, Corollary 0.3, (0.4), and
Lemma 0.4, pp. 2-8.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The M04 curvature-calculus component has exactly the service shape used by
M62; this adapter does not add any geometric assumption. -/
theorem m62CurvatureService_from_M04 : M62CurvatureService.{u} := by
  intro n M _ _ _ g D
  exact LeviCivitaData.intrinsicCurvatureTensorCalculus D

/--
The exact M62 import target: every compact source-admissible Ricci flow has
the corrected spacetime and curve-shortening evolution theory, together with
the zero-safe regularization, integrated curvature bounds, and circle-product
slope laws.
-/
theorem m62CorrectedCurveEvolution (hM04 : M62CurvatureService.{u}) :
    M62CurveEvolutionTheory.{u} := by
  have construction : M62CurvatureService.{u} → M62CurveEvolutionTheory.{u} := by
    intro _ n M _ _ _ _ _ a b F hcompact
    exact M62.nonempty_flowConclusion F hcompact
  exact construction hM04

/-- Concrete assembly from M04's owned component, with no further admission. -/
theorem m62CorrectedCurveEvolution_from_predecessors : M62CurveEvolutionTheory.{u} :=
  m62CorrectedCurveEvolution m62CurvatureService_from_M04

end PoincareMT
