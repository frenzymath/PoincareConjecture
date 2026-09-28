import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderDifferential
import PoincareConjecture.Proofs.M34.Mathlib.ManifoldOpenMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin scale I U)

noncomputable def restrictedSpatialHomeomorph {V : Set C.carrier} (hV : V ⊆ U)
    (s : ℝ) (hs : s ∈ I) : V ≃ₜ (e.forward s hs '' V) := by
  have hmem (y : e.forward s hs '' V) : e.inverse s hs y ∈ V := by
    obtain ⟨x, hx, heq⟩ := y.property
    rw [← heq, e.left_inverse s hs (hV hx)]
    exact hx
  refine {
    toFun := fun x => ⟨e.forward s hs x, mem_image_of_mem _ x.property⟩
    invFun := fun y => ⟨e.inverse s hs y, hmem y⟩
    left_inv := fun x => Subtype.ext (e.left_inverse s hs (hV x.property))
    right_inv := fun y => Subtype.ext
      (e.right_inverse s hs ((image_mono hV) y.property))
    continuous_toFun := ?_
    continuous_invFun := ?_
  }
  · exact ((e.forward_smooth s hs).continuousOn.comp_continuous
      continuous_subtype_val (fun x => hV x.property)).subtype_mk _
  · exact ((e.inverse_smooth s hs).continuousOn.comp_continuous
      continuous_subtype_val (fun y => (image_mono hV) y.property)).subtype_mk _

theorem forward_mfderiv_bijective (hU : IsOpen U) {s : ℝ} (hs : s ∈ I)
    {x : C.carrier} (hx : x ∈ U) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x) := by
  have hfinite : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Module.Finite.of_basis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    exact hfinite
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (e.forward s hs x)) := by
    unfold TangentSpace
    exact hfinite
  have hd : Module.finrank ℝ (TangentSpace (𝓡 3) x) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (e.forward s hs x)) := rfl
  have hi := e.forward_mfderiv_injective hU hs hx
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

theorem isOpen_forward_image (hU : IsOpen U) {V : Set C.carrier}
    (hV : IsOpen V) (hVU : V ⊆ U) {s : ℝ} (hs : s ∈ I) :
    IsOpen (e.forward s hs '' V) :=
  M34.isOpen_image_of_contMDiffOn_mfderiv_bijective hV
    ((e.forward_smooth s hs).mono hVU)
    (fun _ hx => e.forward_mfderiv_bijective hU hs (hVU hx))

noncomputable def spatialOpenPartialHomeomorph (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) :
    OpenPartialHomeomorph C.carrier (F.slice (origin + s / scale)).carrier where
  toFun := e.forward s hs
  invFun := e.inverse s hs
  source := U
  target := e.forward s hs '' U
  map_source' := fun _ hx => mem_image_of_mem _ hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [e.left_inverse s hs hx]
  left_inv' := e.left_inverse s hs
  right_inv' := e.right_inverse s hs
  continuousOn_toFun := (e.forward_smooth s hs).continuousOn
  continuousOn_invFun := (e.inverse_smooth s hs).continuousOn
  open_source := hU
  open_target := e.isOpen_forward_image hU hU (Subset.refl U) hs

theorem spatialOpenPartialHomeomorph_contMDiffOn (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.spatialOpenPartialHomeomorph hU s hs)
      (e.spatialOpenPartialHomeomorph hU s hs).source :=
  e.forward_smooth s hs

theorem spatialOpenPartialHomeomorph_symm_contMDiffOn (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.spatialOpenPartialHomeomorph hU s hs).symm
      (e.spatialOpenPartialHomeomorph hU s hs).target :=
  e.inverse_smooth s hs

theorem isOpenEmbedding_forward_restrict (hU : IsOpen U) {V : Set C.carrier}
    (hV : IsOpen V) (hVU : V ⊆ U) {s : ℝ} (hs : s ∈ I) :
    Topology.IsOpenEmbedding (fun x : V => e.forward s hs x) :=
  (e.isOpen_forward_image hU hV hVU hs).isOpenEmbedding_subtypeVal.comp
    (e.restrictedSpatialHomeomorph hVU s hs).isOpenEmbedding

end PoincareConjecture.GeneralizedFlowCylinder
