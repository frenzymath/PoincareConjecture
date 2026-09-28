import PoincareConjecture.Statements.M62CurveEvolution
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.M62.Sec19_3_Assembly









set_option autoImplicit false

universe u

namespace PoincareConjecture


theorem m62CurvatureService_from_M04 : M62CurvatureService.{u} := by
  intro n M _ _ _ g D
  exact D.curvatureTensorCalculus

































theorem m62CorrectedCurveEvolution (hM04 : M62CurvatureService.{u}) :
    M62CurveEvolutionTheory.{u} := by
  have construction : M62CurvatureService.{u} → M62CurveEvolutionTheory.{u} := by
    intro _ n M _ _ _ _ _ a b F hcompact
    exact M62.nonempty_flowConclusion F hcompact
  exact construction hM04


theorem m62CorrectedCurveEvolution_from_predecessors : M62CurveEvolutionTheory.{u} :=
  m62CorrectedCurveEvolution m62CurvatureService_from_M04

end PoincareConjecture
