import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.SelectedComponent
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem SourceDoubleComponents.exists_injective_source_open
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {sourceSet rimSet : Set E} {e : ι → OpenPartialHomeomorph X V3}
    {f : E → X} {R : Set X} (old : SourceDoubleComponents e f sourceSet rimSet R)
    (x : doubleLocusOn f sourceSet) :
    ∃ U : Set sourceSet, IsOpen U ∧ (⟨x, x.property.1⟩ : sourceSet) ∈ U ∧
      InjOn (fun y : sourceSet ↦ f y) U := by
  obtain ⟨y, hy, hxy, hne⟩ := x.property.2
  obtain ⟨C⟩ := old.crossings x x.property.1 y hy hne hxy
  have hbranch (B : Set E) (hBo : IsOpen ((Subtype.val : sourceSet → E) ⁻¹' B))
      (hBi : IsEmbedding (fun y : B ↦ f y)) (hx : (x : E) ∈ B) :
      ∃ U : Set sourceSet, IsOpen U ∧ (⟨x, x.property.1⟩ : sourceSet) ∈ U ∧
        InjOn (fun y : sourceSet ↦ f y) U := by
    refine ⟨Subtype.val ⁻¹' B, hBo, hx, ?_⟩
    intro a ha b hb hab
    exact Subtype.ext (congrArg (Subtype.val : B → E) (hBi.injective
      (show (fun y : B ↦ f y) ⟨a, ha⟩ = (fun y : B ↦ f y) ⟨b, hb⟩ from hab)))
  rcases C.labels with h | h
  · exact hbranch C.left C.left_open C.left_embedding h.1
  · exact hbranch C.right C.right_open C.right_embedding h.1

theorem SourceDoubleComponents.exists_finite_embedded_source_neighborhood
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {sourceSet rimSet : Set E} [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {A W : Set E}
    {region : Set X} (old : SourceDoubleComponents e f sourceSet rimSet region)
    (hf : PolyhedralPLInCharts e f sourceSet) (hA : IsCompact A)
    (hAG : A ⊆ doubleLocusOn f sourceSet) (hinj : InjOn f A)
    (hW : IsOpen ((Subtype.val : sourceSet → E) ⁻¹' W)) (hAW : A ⊆ W) :
    ∃ (P : SimplicialComplex ℝ E) (U : Set sourceSet),
      P.faces.Finite ∧ P.space ⊆ sourceSet ∩ W ∧
      IsOpen U ∧ (Subtype.val : sourceSet → E) ⁻¹' A ⊆ U ∧
      Subtype.val '' U ⊆ P.space ∧
      IsEmbedding (fun x : P.space ↦ f x) ∧ PolyhedralPLInCharts e f P.space := by
  have hAD : A ⊆ sourceSet := fun _ hx ↦ (hAG hx).1
  have hAimage : (Subtype.val : sourceSet → E) '' ((Subtype.val : sourceSet → E) ⁻¹' A) = A :=
    image_preimage_eq_iff.mpr (fun x hx ↦ ⟨⟨x, hAD hx⟩, rfl⟩)
  have hAc : IsCompact ((Subtype.val : sourceSet → E) ⁻¹' A) :=
    IsEmbedding.subtypeVal.isCompact_iff.mpr (hAimage.symm ▸ hA)
  have hfc : Continuous (fun x : sourceSet ↦ f x) :=
    hf.continuousOn.comp_continuous continuous_subtype_val (fun x ↦ x.property)
  have hinj' : InjOn (fun x : sourceSet ↦ f x) ((Subtype.val : sourceSet → E) ⁻¹' A) :=
    fun _ hx _ hy hxy ↦ Subtype.ext (hinj hx hy hxy)
  obtain ⟨V, hVo, hAV, hVi⟩ := hinj'.exists_isOpen_superset hAc
    (fun x _ ↦ hfc.continuousAt) (by
      intro x hx
      obtain ⟨U, hUo, hxU, hUi⟩ := old.exists_injective_source_open ⟨x, hAG hx⟩
      exact ⟨U, hUo.mem_nhds hxU, hUi⟩)
  obtain ⟨O, hOo, hOV⟩ := isOpen_induced_iff.mp (hVo.inter hW)
  have hAO : A ⊆ O := by
    intro x hx
    exact hOV.symm.subset ⟨hAV (show (⟨x, hAD hx⟩ : sourceSet) ∈ Subtype.val ⁻¹' A from hx), hAW hx⟩
  obtain ⟨N, hN, hAN, hNO⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed hA hOo hAO
  let Q := old.source
  have hQ := old.source_finite
  have hQs : Q.space = sourceSet := old.source_space
  obtain ⟨P, hP, hPs⟩ := N.exists_finite_triangulation_inter Q hN hQ
  have hPD : P.space ⊆ sourceSet := fun _ hx ↦ hQs ▸ (hPs.subset hx).2
  have hPV (x : P.space) : (⟨x, hPD x.property⟩ : sourceSet) ∈ V ∩ Subtype.val ⁻¹' W :=
    hOV.subset (hNO (hPs.subset x.property).1)
  let U : Set sourceSet := Subtype.val ⁻¹' interior N.space
  have hUi : Subtype.val '' U ⊆ P.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPs.symm.subset ⟨interior_subset hx, hQs.symm ▸ x.property⟩
  have hPL := hf.restrict_finite P hP hPD
  let : CompactSpace P.space := isCompact_iff_compactSpace.mp (P.isCompact_space_of_finite hP)
  refine ⟨P, U, hP, fun x hx ↦ ⟨hPD hx, (hPV ⟨x, hx⟩).2⟩,
    isOpen_interior.preimage continuous_subtype_val, fun x hx ↦ hAN hx, hUi, ?_, hPL⟩
  have hinjP : Function.Injective (fun x : P.space ↦ f x) := by
    intro x y hxy
    exact Subtype.ext (congrArg (Subtype.val : sourceSet → E) (hVi (hPV x).1 (hPV y).1 hxy))
  exact ((hPL.continuousOn.comp_continuous continuous_subtype_val
    (fun x ↦ x.property)).isClosedEmbedding hinjP).isEmbedding

end PoincareConjecture.M76.Dehn.Annuli
