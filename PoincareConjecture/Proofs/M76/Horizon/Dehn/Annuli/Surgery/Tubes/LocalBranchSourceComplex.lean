import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.ComponentBranchModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalBranchSourceComplex

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "V3" => (Fin 3 → ℝ)

theorem RawSourceCrossing.face_in_one_branch
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {x y : E}
    (C : RawSourceCrossing e f S R x y) (K : SimplicialComplex ℝ E)
    (hKD : K.space ⊆ S) (hKC : MapsTo f K.space C.chart.source)
    (s : Finset E) (hs : s ∈ K.faces) :
    convexHull ℝ (s : Set E) ⊆ C.left ∨ convexHull ℝ (s : Set E) ⊆ C.right := by
  let A := convexHull ℝ (s : Set E)
  have hAD : A ⊆ S := (K.convexHull_subset_space hs).trans hKD
  have hAi : (Subtype.val : S → E) '' (Subtype.val ⁻¹' A) = A := by
    ext z
    exact ⟨fun ⟨u, hu, heq⟩ => heq ▸ hu, fun hz => ⟨⟨z, hAD hz⟩, hz, rfl⟩⟩
  have hconn : IsPreconnected ((Subtype.val : S → E) ⁻¹' A) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hAi]
    exact (convex_convexHull ℝ _).isPreconnected
  have hcover : (Subtype.val : S → E) ⁻¹' A ⊆
      Subtype.val ⁻¹' C.left ∪ Subtype.val ⁻¹' C.right := by
    intro z hz
    exact C.whole_preimage.subset ⟨z.property, hKC (K.convexHull_subset_space hs hz)⟩
  have hdis : Disjoint ((Subtype.val : S → E) ⁻¹' C.left) (Subtype.val ⁻¹' C.right) :=
    C.disjoint.preimage Subtype.val
  rcases hconn.subset_or_subset C.left_open C.right_open hdis hcover with hL | hR
  · exact Or.inl (fun z hz => hL (a := ⟨z, hAD hz⟩) hz)
  · exact Or.inr (fun z hz => hR (a := ⟨z, hAD hz⟩) hz)

theorem RawSourceCrossing.vertexSubcomplex_space
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {x y : E}
    (C : RawSourceCrossing e f S R x y) (K : SimplicialComplex ℝ E)
    (hKD : K.space ⊆ S) (hKC : MapsTo f K.space C.chart.source) :
    (K.vertexSubcomplex C.left).space = K.space ∩ C.left ∧
    (K.vertexSubcomplex C.right).space = K.space ∩ C.right := by
  have hside (A B : Set E) (hdis : Disjoint A B)
      (hfaces : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ A ∨
        convexHull ℝ (s : Set E) ⊆ B) : (K.vertexSubcomplex A).space = K.space ∩ A := by
    ext z
    constructor
    · intro hz
      obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp hz
      refine ⟨K.convexHull_subset_space hs.1 hzs, ?_⟩
      rcases hfaces s hs.1 with hA | hB
      · exact hA hzs
      · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs.1
        exact (disjoint_left.mp hdis (hs.2 v hv) (hB (subset_convexHull ℝ _ hv))).elim
    · rintro ⟨hz, hzA⟩
      obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp hz
      have hsA : convexHull ℝ (s : Set E) ⊆ A :=
        (hfaces s hs).resolve_right (fun hB => disjoint_left.mp hdis hzA (hB hzs))
      exact SimplicialComplex.mem_space_iff.mpr ⟨s,
        ⟨hs, fun v hv => hsA (subset_convexHull ℝ _ hv)⟩, hzs⟩
  exact ⟨hside C.left C.right C.disjoint (C.face_in_one_branch K hKD hKC),
    hside C.right C.left C.disjoint.symm (fun s hs => (C.face_in_one_branch K hKD hKC s hs).symm)⟩

end PoincareConjecture.M76.Dehn.Annuli
