import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteLabelSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_finite_label_homeomorph
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {S : Set X} (HB : K.space ≃ₜ S) (q : C(X, Y))
    {D : Set Y} (hD : D.Finite) (hS : S = q ⁻¹' D)
    (b : E → X) (hb : ∀ x : K.space, b x = (HB x : X))
    {v : Y} (hv : v ∈ D) :
    ∃ (J : SimplicialComplex ℝ E) (H : J.space ≃ₜ (q ⁻¹' {v} : Set X)),
      J.faces.Finite ∧ J ≤ K ∧
      J.space = K.space ∩ (fun x => q (b x)) ⁻¹' {v} ∧
      (∀ x : J.space, (H x : X) = b x) ∧
      IsClopen {x : K.space | q (b x) = v} := by
  classical
  let label : E → Y := fun x => q (b x)
  have hbcont : Continuous (fun x : K.space => b x) :=
    (continuous_subtype_val.comp HB.continuous).congr (fun x => (hb x).symm)
  have hlabel : ContinuousOn label K.space :=
    continuousOn_iff_continuous_domRestrict.mpr (q.continuous.comp hbcont)
  have hlabels : MapsTo label K.space D := by
    intro x hx
    change q (b x) ∈ D
    rw [hb ⟨x, hx⟩]
    exact hS.subset (HB ⟨x, hx⟩).property
  let J := K.vertexSubcomplex {x | label x = v}
  have hJ : J.faces.Finite := K.vertexSubcomplex_finite _ hK
  have hJL : J ≤ K := K.vertexSubcomplex_le _
  have hJs : J.space = K.space ∩ label ⁻¹' {v} :=
    K.vertexSubcomplex_space_eq_finite_label hlabel hD hlabels v
  have hJK : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJL
  let i : J.space → K.space := Set.inclusion hJK
  have hi : Topology.IsEmbedding i := Topology.IsEmbedding.inclusion hJK
  let t : J.space → X := fun x => (HB (i x) : X)
  have ht : Topology.IsEmbedding t :=
    Topology.IsEmbedding.subtypeVal.comp (HB.isEmbedding.comp hi)
  have htLevel (x : J.space) : t x ∈ q ⁻¹' {v} := by
    change q (HB (i x)) = v
    rw [← hb (i x)]
    exact (hJs.subset x.property).2
  let f : J.space → (q ⁻¹' {v} : Set X) := fun x => ⟨t x, htLevel x⟩
  have hf : Topology.IsEmbedding f := ht.codRestrict _ htLevel
  have hsurj : Function.Surjective f := by
    intro y
    have hyS : (y : X) ∈ S := by
      rw [hS]
      change q (y : X) ∈ D
      rw [show q (y : X) = v from y.property]
      exact hv
    let x : K.space := HB.symm ⟨y, hyS⟩
    have hHx : HB x = ⟨y, hyS⟩ := HB.apply_symm_apply ⟨y, hyS⟩
    have hxb : b x = (y : X) :=
      (hb x).trans (congrArg (Subtype.val : S → X) hHx)
    have hxJ : (x : E) ∈ J.space := by
      apply hJs.symm.subset
      refine ⟨x.property, ?_⟩
      change q (b x) = v
      rw [hxb]
      exact y.property
    refine ⟨⟨x, hxJ⟩, ?_⟩
    apply Subtype.ext
    change (HB (i ⟨x, hxJ⟩) : X) = (y : X)
    have hix : i ⟨x, hxJ⟩ = x := Subtype.ext rfl
    rw [hix]
    exact congrArg (Subtype.val : S → X) hHx
  let H : J.space ≃ₜ (q ⁻¹' {v} : Set X) := hf.toHomeomorphOfSurjective hsurj
  refine ⟨J, H, hJ, hJL, hJs, ?_, K.isClopen_finite_label_level hlabel hD hlabels v⟩
  intro x
  change t x = b x
  exact (hb (i x)).symm

end Geometry.SimplicialComplex
