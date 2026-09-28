import PoincareConjecture.Proofs.M34.Standard.LocalPullbackRealization
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderDifferential
import PoincareConjecture.Proofs.M13.Metric











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder



theorem exists_local_coordinate_realization
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier)
    {s : ℝ} (hs : s ∈ K) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target ∧ (extChartAt (𝓡 3) q).symm p ∈ U) :
    ∃ (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (_D : LeviCivitaData g) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V ∧ p ∈ V ∧
        V ⊆ (extChartAt (𝓡 3) q).target ∩ (extChartAt (𝓡 3) q).symm ⁻¹' U ∧
        ∀ x ∈ V, ∀ a b : Fin 3,
          g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) =
          blowupPullbackCoefficient e q a b (s, x) := by
  let c := extChartAt (𝓡 3) q
  let f := e.forward s hs
  let W := c.target ∩ c.symm ⁻¹' U
  let gS : RiemannianMetric 3 (F.slice (origin + s / scale)).carrier :=
    M13.scaleSmoothMetric (F.metric (origin + s / scale)) scale e.scale_pos
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
  obtain ⟨g, D, V, hVo, hpV, hV, heq⟩ :=
    gS.exists_local_immersive_pullback_realization (f ∘ c.symm) hW hp
      (fun x hx => ((hf x hx).comp x (hc x hx)).contMDiffWithinAt)
      (fun x hx => by
        rw [hd x hx]
        have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible := by
          simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
            isInvertible_mfderivWithin_extChartAt_symm hx.1
        exact (e.forward_mfderiv_injective hU hs hx.2).comp hi.injective)
  refine ⟨g, D, V, hVo, hpV, hV, ?_⟩
  intro x hx a b
  rw [heq x hx]
  simp only [blowupPullbackCoefficient, dif_pos hs]
  change scale * (F.metric (origin + s / scale)).inner (f (c.symm x))
    (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin 3) ℝ b)) = _
  rw [hd x (hV hx)]
  rfl

end PoincareConjecture.GeneralizedFlowCylinder
