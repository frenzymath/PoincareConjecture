import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteLabelHomeomorph
import Mathlib.Topology.Clopen









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_clopen_subcomplex_homeomorph
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {S M : Set X} (HB : K.space ≃ₜ S) (hMS : M ⊆ S)
    (hclopen : IsClopen ((Subtype.val : S → X) ⁻¹' M))
    (b : E → X) (hb : ∀ x : K.space, b x = (HB x : X)) :
    ∃ (J : SimplicialComplex ℝ E) (H : J.space ≃ₜ M),
      J.faces.Finite ∧ J ≤ K ∧ J.space = K.space ∩ b ⁻¹' M ∧
      (∀ x : J.space, (H x : X) = b x) ∧
      IsClopen ((Subtype.val : K.space → E) ⁻¹' (b ⁻¹' M)) := by
  classical
  let U : Set E := b ⁻¹' M
  have hU : IsClopen ((Subtype.val : K.space → E) ⁻¹' U) := by
    convert hclopen.preimage HB.continuous using 1
    ext x
    change b x ∈ M ↔ (HB x : X) ∈ M
    rw [hb x]
  have hlabel : ContinuousOn U.boolIndicator K.space :=
    (continuousOn_boolIndicator_iff_isClopen K.space U).mpr hU
  let J := K.vertexSubcomplex {x | U.boolIndicator x = true}
  have hJs : J.space = K.space ∩ U := by
    rw [K.vertexSubcomplex_space_eq_finite_label hlabel (finite_univ : (univ : Set Bool).Finite)
      (mapsTo_univ _ _) true, preimage_boolIndicator_true]
  have hJK : J ≤ K := K.vertexSubcomplex_le _
  have hsub : J.space ⊆ K.space := space_subset_of_le hJK
  let i : J.space → K.space := Set.inclusion hsub
  let t : J.space → X := fun x => (HB (i x) : X)
  have ht : Topology.IsEmbedding t := Topology.IsEmbedding.subtypeVal.comp
    (HB.isEmbedding.comp (Topology.IsEmbedding.inclusion hsub))
  have htM (x : J.space) : t x ∈ M := by
    rw [show t x = b x from (hb (i x)).symm]
    exact (hJs.subset x.property).2
  let f : J.space → M := fun x => ⟨t x, htM x⟩
  have hf : Topology.IsEmbedding f := ht.codRestrict _ htM
  have hsurj : Function.Surjective f := by
    intro y
    let x := HB.symm ⟨y, hMS y.property⟩
    have hxb : b x = (y : X) := (hb x).trans
      (congrArg Subtype.val (HB.apply_symm_apply ⟨y, hMS y.property⟩))
    have hxJ : (x : E) ∈ J.space := hJs.symm.subset
      ⟨x.property, by change b x ∈ M; rw [hxb]; exact y.property⟩
    refine ⟨⟨x, hxJ⟩, ?_⟩
    apply Subtype.ext
    change (HB (i ⟨x, hxJ⟩) : X) = y
    exact (hb (i ⟨x, hxJ⟩)).symm.trans hxb
  exact ⟨J, hf.toHomeomorphOfSurjective hsurj,
    K.vertexSubcomplex_finite _ hK, hJK, hJs, fun x => (hb (i x)).symm, hU⟩

end Geometry.SimplicialComplex
