import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.Uniqueness
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.RotatedFlow










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34




theorem partialStandardCapFlow_rotation_invariant (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) (e : StandardCylindricalEnd g0.metric)
    {t : ℝ} (ht : t ∈ Ico 0 F.lifetime)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) (u v : TangentSpace (𝓡 3) x) :
    (F.flow.metric t).inner (standardRotation A x)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
        (F.flow.metric t).inner x u v := by
  have h := partialStandardCapFlow_metric_unique P E0
    (PartialStandardCapFlow.rotatedPartialFlow F A) F e ⟨ht, ht⟩
  calc
    _ = ((PartialStandardCapFlow.rotatedPartialFlow F A).flow.metric t).inner x u v :=
      (PartialStandardCapFlow.rotatedPartialFlow_metric_inner F A t x u v).symm
    _ = _ := congrArg (fun G : RiemannianMetric 3 StandardCapSpace => G.inner x u v) h

end PoincareConjecture.M34
