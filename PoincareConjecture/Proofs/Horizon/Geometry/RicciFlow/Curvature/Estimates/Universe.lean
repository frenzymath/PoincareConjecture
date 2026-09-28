import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Local
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture



theorem RicciFlowCurvatureTheory.local_derivative_estimates_small
    (hC : RicciFlowCurvatureTheory.{u}) : LocalCurvatureDerivativeEstimates.{0} := by
  intro n k K α r hK hα hr
  obtain ⟨C, hCpos, hbound⟩ := hC.local_derivative_estimates n k K α r hK hα hr
  refine ⟨C, hCpos, ?_⟩
  intro M _ _ _ _ _ T hT hTK F p hcompact hcurv t ht x hx
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  let : IsManifold (𝓡 n) ∞ (ULift.{u} M) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) M
  let e : ULift.{u} M ≃ₜ M := Homeomorph.ulift
  let : SecondCountableTopology (ULift.{u} M) := e.isEmbedding.secondCountableTopology
  let G : RicciFlow n (ULift.{u} M) (Icc 0 T) := F.ulift
  have hball (ρ : ℝ) :
      (G.metric 0).ball (e.symm p) ρ = e ⁻¹' (F.metric 0).ball p ρ := by
    ext y
    simp only [G, RiemannianMetric.ball, mem_preimage, mem_ofPred_eq,
      F.ulift_edist]
    rfl
  have hcompact' : IsCompact (closure ((G.metric 0).ball (e.symm p) r)) := by
    rw [hball]
    rw [← e.preimage_closure]
    exact e.isCompact_preimage.mpr hcompact
  have hb := hbound (ULift.{u} M) T hT hTK G (e.symm p) hcompact'
    (fun s hs y hy => by
      dsimp only [G]
      rw [F.ulift_curvatureTensorNorm]
      exact hcurv s hs (e y) (by simpa only [hball, mem_preimage] using hy))
    t ht (e.symm x) (by simpa only [hball, mem_preimage, e.apply_symm_apply] using hx)
  have hxdown : (e.symm x).down = x := rfl
  simpa only [G, F.ulift_curvatureDerivativeNorm, hxdown] using hb

end PoincareConjecture
