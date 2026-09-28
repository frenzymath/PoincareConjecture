import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderRealization











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace FlowCarrier



theorem exists_local_isometry_of_coordinate_germ
    {n : ℕ} (C : FlowCarrier n) (gM : C.metric)
    (q : C.carrier) (t : ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p ∈ (extChartAt (𝓡 n) q).target)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin n,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      C.coordinateCoefficient q (fun _ y v w => C.metricInner gM y v w) a b (t, x)) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ p ∈ V ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) q).symm V ∧
      ∀ x ∈ V, ∀ v w : TangentSpace (𝓡 n) x,
        gE.inner x v w = gM.inner ((extChartAt (𝓡 n) q).symm x)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm x v)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm x w) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 n) q
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp
    (inter_mem (extChartAt_target_mem_nhds' hp) h)
  refine ⟨V, hVo, hpV, ?_, ?_⟩
  · exact fun x hx => (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q
      (hV hx).1).contMDiffAt (extChartAt_target_mem_nhds' (hV hx).1)
        |>.contMDiffWithinAt
  · intro x hx v w
    have hB : gE.euclideanCoefficients x = gM.pullbackCoefficients c.symm x := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro a
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      exact (hV hx).2 a
    exact congrArg (fun B => B v w) hB

end FlowCarrier

namespace GeneralizedFlowCylinder




theorem exists_local_homothety_of_coordinate_germ
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier)
    {s : ℝ} (hs : s ∈ K) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target ∧ (extChartAt (𝓡 3) q).symm p ∈ U)
    (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin 3,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = blowupPullbackCoefficient e q a b (s, x)) :
    ∃ V : Set (EuclideanSpace ℝ (Fin 3)), IsOpen V ∧ p ∈ V ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞
        (e.forward s hs ∘ (extChartAt (𝓡 3) q).symm) V ∧
      ∀ x ∈ V, ∀ v w : TangentSpace (𝓡 3) x,
        gE.inner x v w = scale *
          (F.metric (origin + s / scale)).inner
            ((e.forward s hs ∘ (extChartAt (𝓡 3) q).symm) x)
            (mfderiv (𝓡 3) (𝓡 3)
              (e.forward s hs ∘ (extChartAt (𝓡 3) q).symm) x v)
            (mfderiv (𝓡 3) (𝓡 3)
              (e.forward s hs ∘ (extChartAt (𝓡 3) q).symm) x w) := by
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
  refine ⟨V, hVo, hpV, ?_, ?_⟩
  · exact fun x hx => ((hf x (hV hx).1).comp x (hc x (hV hx).1)).contMDiffWithinAt
  · intro x hx v w
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

end GeneralizedFlowCylinder
end PoincareConjecture
