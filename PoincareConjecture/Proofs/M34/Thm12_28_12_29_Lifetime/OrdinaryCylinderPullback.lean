import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryGeometry











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

variable {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {K : Set ℝ} {U : Set C.carrier}



noncomputable def ordinaryChapter11CylinderSpatialMap
    (e : GeneralizedFlowCylinder (G) C origin scale K U)
    (s0 : ℝ) (hs0 : s0 ∈ K) (x : C.carrier) : M :=
  ordinaryChapter11Projection (I := I) (F := F) R (e.pointMap s0 hs0 x)



theorem ordinaryChapter11CylinderSpatialMap_contMDiffOn
    (e : GeneralizedFlowCylinder (G) C origin scale K U) {s0 : ℝ} (hs0 : s0 ∈ K) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ordinaryChapter11CylinderSpatialMap R e s0 hs0) U := by
  intro x hx
  let t : I.domain := ⟨origin + s0 / scale,
    ordinaryChapter11Point_time_mem (I := I) (F := F) R (e.pointMap s0 hs0 x)⟩
  have heq : ordinaryChapter11CylinderSpatialMap R e s0 hs0 =
      (R.product.sliceIdentification t).symm ∘ e.forward s0 hs0 := by
    funext y
    exact (ordinaryChapter11_inverse_projection (I := I) (F := F) R t
      (e.forward s0 hs0 y)).symm
  rw [heq]
  exact ((R.product.sliceIdentification t).symm.contMDiff.comp_contMDiffOn
    (e.forward_smooth s0 hs0)) x hx




theorem ordinaryChapter11Cylinder_forward_eq
    (e : GeneralizedFlowCylinder (G) C origin scale K U) (hK : IsPreconnected K)
    {s0 s : ℝ} (hs0 : s0 ∈ K) (hs : s ∈ K)
    (ht : origin + s / scale ∈ I.domain) :
    EqOn (e.forward s hs)
      ((R.product.sliceIdentification ⟨origin + s / scale, ht⟩) ∘
        ordinaryChapter11CylinderSpatialMap R e s0 hs0) U := by
  intro x hx
  have hp := ordinaryChapter11Projection_cylinder_eq (I := I) (F := F) R e hK hx hs hs0
  exact (ordinaryChapter11_identification_projection (I := I) (F := F) R
    ⟨origin + s / scale, ht⟩ (e.forward s hs x)).symm.trans
      (congrArg (R.product.sliceIdentification ⟨origin + s / scale, ht⟩) hp)

set_option backward.isDefEq.respectTransparency false in



theorem ordinaryChapter11Cylinder_pullbackInner_eq
    (e : GeneralizedFlowCylinder (G) C origin scale K U) (hU : IsOpen U) (hK : IsPreconnected K)
    {s0 s : ℝ} (hs0 : s0 ∈ K) (hs : s ∈ K) {x : C.carrier} (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner s hs x v w =
      scale * (F.metric (origin + s / scale)).inner
        (ordinaryChapter11CylinderSpatialMap R e s0 hs0 x)
        (mfderiv (𝓡 3) (𝓡 3) (ordinaryChapter11CylinderSpatialMap R e s0 hs0) x v)
        (mfderiv (𝓡 3) (𝓡 3) (ordinaryChapter11CylinderSpatialMap R e s0 hs0) x w) := by
  let t : I.domain := ⟨origin + s / scale,
    ordinaryChapter11Point_time_mem (I := I) (F := F) R (e.pointMap s hs x)⟩
  let f := ordinaryChapter11CylinderSpatialMap R e s0 hs0
  have heq := ordinaryChapter11Cylinder_forward_eq R e hK hs0 hs t.property
  have hlocal : e.forward s hs =ᶠ[𝓝 x] (R.product.sliceIdentification t) ∘ f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq hy
  have hf := ((ordinaryChapter11CylinderSpatialMap_contMDiffOn R e hs0 x hx).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd := hlocal.mfderiv_eq.trans
    (mfderiv_comp x ((R.product.sliceIdentification t).mdifferentiable (by simp) _) hf)
  unfold GeneralizedFlowCylinder.pullbackInner
  rw [hd, heq hx]
  exact congrArg (fun a : ℝ => scale * a)
    (R.product.sliceMetric_eq t (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))

end PoincareConjecture.M34
