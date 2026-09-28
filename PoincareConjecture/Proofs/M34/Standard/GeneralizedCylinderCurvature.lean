import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderRealization
import PoincareConjecture.Proofs.M34.Standard.LocalHomothetyCurvature











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option backward.isDefEq.respectTransparency false in


theorem curvatures_eq_of_coordinate_germ
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier)
    {s : ℝ} (hs : s ∈ K) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target ∧ (extChartAt (𝓡 3) q).symm p ∈ U)
    (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin 3,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = blowupPullbackCoefficient e q a b (s, x)) :
    DE.scalarCurvature p = F.scalar (e.pointMap s hs ((extChartAt (𝓡 3) q).symm p)) / scale ∧
    DE.curvatureTensorNorm p =
      F.curvatureNorm (e.pointMap s hs ((extChartAt (𝓡 3) q).symm p)) / scale := by
  let c := extChartAt (𝓡 3) q
  let f := e.forward s hs
  let W := c.target ∩ c.symm ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  have hc (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx.1).contMDiffAt
      (extChartAt_target_mem_nhds' hx.1)
  have hf (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (c.symm x) :=
    (e.forward_smooth s hs _ hx.2).contMDiffAt (hU.mem_nhds hx.2)
  have hd (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ W) :
      mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) x =
        (mfderiv (𝓡 3) (𝓡 3) f (c.symm x)).comp
          (mfderiv (𝓡 3) (𝓡 3) c.symm x) :=
    mfderiv_comp x ((hf x hx).mdifferentiableAt (by simp))
      ((hc x hx).mdifferentiableAt (by simp))
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (inter_mem (hW.mem_nhds hp) h)
  have hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f ∘ c.symm) V :=
    fun x hx => ((hf x (hV hx).1).comp x (hc x (hV hx).1)).contMDiffWithinAt
  have hmetric (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ V)
      (v w : TangentSpace (𝓡 3) x) :
      gE.inner x v w = scale * (F.metric (origin + s / scale)).inner (f (c.symm x))
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) x v)
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) x w) := by
    have hB : gE.euclideanCoefficients x =
        scale • (F.metric (origin + s / scale)).pullbackCoefficients (f ∘ c.symm) x := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
      intro a
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
      intro b
      change gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = _
      rw [(hV hx).2 a b]
      simp only [blowupPullbackCoefficient, dif_pos hs]
      change _ = scale * (F.metric (origin + s / scale)).inner (f (c.symm x))
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin 3) ℝ a))
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin 3) ℝ b))
      rw [hd x (hV hx).1]
      rfl
    exact congrArg (fun B => B v w) hB
  exact ⟨DE.scalarCurvature_eq_of_local_homothety (F.connection (origin + s / scale))
    e.scale_pos hVo hφ hmetric hpV,
    DE.curvatureTensorNorm_eq_of_local_homothety (F.connection (origin + s / scale))
      e.scale_pos hVo hφ hmetric hpV⟩

end PoincareConjecture.GeneralizedFlowCylinder
