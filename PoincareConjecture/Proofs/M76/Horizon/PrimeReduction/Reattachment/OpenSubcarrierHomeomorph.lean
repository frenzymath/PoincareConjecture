import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem exists_open_subcarrier_partial_homeomorph
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {U : Set X} [Nonempty U] (hU : IsOpen U)
    {V W : Set E} (hVW : V ⊆ W)
    (hV : IsOpen ((Subtype.val : W → E) ⁻¹' V)) (H : U ≃ₜ V) :
    ∃ M : OpenPartialHomeomorph X W,M.source = U ∧
      M.target = (Subtype.val : W → E) ⁻¹' V ∧
      ∀ x : U,(M x : E) = H x := by
  let A := (Subtype.val : W → E) ⁻¹' V
  let K : V ≃ₜ A := {
    toFun := fun x => ⟨⟨x,hVW x.property⟩,x.property⟩
    invFun := fun x => ⟨x.val.val,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let f : U → W := fun x => ⟨H x,hVW (H x).property⟩
  have hf : Topology.IsOpenEmbedding f :=
    hV.isOpenEmbedding_subtypeVal.comp (H.trans K).isOpenEmbedding
  let j := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → X)
  let k := hf.toOpenPartialHomeomorph f
  let M := j.symm.trans k
  have hrange : range f = (Subtype.val : W → E) ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact (H x).property
    · intro hy
      obtain ⟨x,hx⟩ := H.surjective ⟨y,hy⟩
      exact ⟨x,Subtype.ext (congrArg (fun z : V => (z : E)) hx)⟩
  refine ⟨M,?_,?_,?_⟩
  · simp only [M,OpenPartialHomeomorph.trans_source,j,k,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      OpenPartialHomeomorph.symm_source,preimage_univ,inter_univ,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,Subtype.range_coe]
  · simpa only [M,OpenPartialHomeomorph.trans_target,j,k,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      OpenPartialHomeomorph.symm_target,preimage_univ,inter_univ,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,image_univ] using hrange
  · intro x
    have hx : j.symm (x : X) = x := j.left_inv (mem_univ x)
    change (H (j.symm x) : E) = H x
    rw [hx]

theorem image_mark_of_open_subcarrier_partial_homeomorph
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {U R : Set X} {V W T : Set E}
    (H : U ≃ₜ V) (M : OpenPartialHomeomorph X W)
    (hvalues : ∀ x : U,(M x : E) = H x)
    (hRU : R ⊆ U) (hTV : T ⊆ V)
    (hmark : ∀ x : U,(x : X) ∈ R ↔ (H x : E) ∈ T) :
    M '' R = (Subtype.val : W → E) ⁻¹' T := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change (M x : E) ∈ T
    rw [hvalues ⟨x,hRU hx⟩]
    exact (hmark ⟨x,hRU hx⟩).mp hx
  · intro hy
    let x : U := H.symm ⟨y,hTV hy⟩
    have hHx : (H x : E) = y := congrArg Subtype.val (H.apply_symm_apply ⟨y,hTV hy⟩)
    refine ⟨x,(hmark x).mpr (hHx.symm ▸ hy),?_⟩
    exact Subtype.ext ((hvalues x).trans hHx)

end PoincareConjecture.M76
