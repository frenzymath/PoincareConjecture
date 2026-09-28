import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Mathlib.ClopenSubcomplexHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.FiniteClosedPartition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem exists_finite_component_bicollar
    {E V X ι σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [Finite σ]
    {e : ι → OpenPartialHomeomorph X V}
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    {S : Set X} (HB : L.space ≃ₜ S)
    (M : σ → Set X) (hclosed : ∀ i, IsClosed (M i))
    (hdisjoint : Pairwise fun i j => Disjoint (M i) (M j))
    (hunion : (⋃ i, M i) = S) (c : E × ℝ → X)
    {r : ℝ} (hr : 0 < r)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hbase : ∀ z : L.space, c ((z : E), 0) = HB z)
    (hopen : IsOpen (c '' (L.space ×ˢ Ioo (-r) r))) (i : σ) :
    ∃ (J : SimplicialComplex ℝ E) (H : J.space ≃ₜ M i),
      J.faces.Finite ∧ J ≤ L ∧
      J.space = {x | x ∈ L.space ∧ c (x, 0) ∈ M i} ∧
      (∀ x : J.space, c ((x : E), 0) = H x) ∧
      PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r) ∧
      Topology.IsEmbedding (fun z : (J.space ×ˢ Icc (-r) r : Set (E × ℝ)) => c z) ∧
      IsOpen (c '' (J.space ×ˢ Ioo (-r) r)) := by
  have hMS : M i ⊆ S := (subset_iUnion M i).trans_eq hunion
  have hclopen : IsClopen ((Subtype.val : S → X) ⁻¹' M i) := by
    subst S
    exact Poincare.Topology.isClopen_part_of_finite_closed_partition M hclosed hdisjoint i
  obtain ⟨J, H, hJ, hJL, hJs, hH, hclopenJ⟩ :=
    L.exists_clopen_subcomplex_homeomorph hL HB hMS hclopen (fun x => c (x, 0)) hbase
  have hsub : J.space ⊆ L.space := SimplicialComplex.space_subset_of_le hJL
  have hprod : J.space ×ˢ Icc (-r) r ⊆ L.space ×ˢ Icc (-r) r :=
    prod_mono hsub Subset.rfl
  obtain ⟨K, hK, hKs⟩ := J.exists_finite_interval_product hJ (show -r < r by linarith)
  have hPL : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r) :=
    hKs ▸ hc.restrict_finite K hK (hKs.subset.trans hprod)
  refine ⟨J, H, hJ, hJL, hJs, fun x => (hH x).symm, hPL,
    hi.comp (Topology.IsEmbedding.inclusion hprod), ?_⟩
  let P : Set (E × ℝ) := L.space ×ˢ Icc (-r) r
  let base : P → L.space := fun z => ⟨z.1.1, z.property.1⟩
  let time : P → ℝ := fun z => z.1.2
  have hbaseCont : Continuous base :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have htimeCont : Continuous time := continuous_snd.comp continuous_subtype_val
  let A : Set P := base ⁻¹' ((Subtype.val : L.space → E) ⁻¹'
    ((fun x => c (x, 0)) ⁻¹' M i)) ∩ time ⁻¹' Ioo (-r) r
  have hA : IsOpen A :=
    (hclopenJ.2.preimage hbaseCont).inter (isOpen_Ioo.preimage htimeCont)
  let f : P → X := fun z => c z
  have hAW : f '' A ⊆ c '' (L.space ×ˢ Ioo (-r) r) := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨z.property.1, hz.2⟩, rfl⟩
  have hWf : c '' (L.space ×ˢ Ioo (-r) r) ⊆ range f := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩
  have himage : f '' A = c '' (J.space ×ˢ Ioo (-r) r) := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact ⟨z, ⟨hJs.symm.subset ⟨z.property.1, hz.1⟩, hz.2⟩, rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      refine ⟨⟨z, hsub hz.1, hz.2.1.le, hz.2.2.le⟩, ?_, rfl⟩
      exact ⟨(hJs.subset hz.1).2, hz.2⟩
  rw [← himage]
  exact hi.isInducing.isOpen_image_of_subset_open hA hopen hAW hWf

end PoincareConjecture.M76
