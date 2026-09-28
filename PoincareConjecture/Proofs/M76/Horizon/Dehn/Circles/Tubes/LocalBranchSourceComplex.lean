import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentBranchModel
import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1


theorem finitePL_exists_source_complex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : Set E} {f : E → F}
    (hf : FinitePiecewiseAffineOn f S)
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧ T.space = S ∩ f ⁻¹' K.space := by
  classical
  let : Finite K.faces := hK.to_subtype
  have hpiece (s : K.faces) : ∃ T : SimplicialComplex ℝ E,
      T.faces.Finite ∧ T.space = S ∩ f ⁻¹' convexHull ℝ (s.val : Set F) := by
    obtain ⟨cuts, hcuts⟩ := s.val.exists_affine_halfspaces_convexHull (K.indep s.property)
    obtain ⟨T, hT, hTs⟩ := hf.exists_finite_halfspace_preimage cuts
    refine ⟨T, hT, hTs.trans ?_⟩
    rw [hcuts]
    rfl
  choose T hT hTs using hpiece
  obtain ⟨L, hL, hLs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion T hT
  refine ⟨L, hL, hLs.trans ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs⟩ := mem_iUnion.mp hz
    rw [hTs s] at hs
    exact ⟨hs.1, K.convexHull_subset_space s.property hs.2⟩
  · intro hz
    obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp hz.2
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, (hTs ⟨s, hs⟩).symm ▸ ⟨hz.1, hzs⟩⟩



theorem RawCrossingChart.face_in_one_branch
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X} {x y : V2}
    (C : RawCrossingChart e f R x y) (K : SimplicialComplex ℝ V2)
    (hKD : K.space ⊆ D2) (hKC : MapsTo f K.space C.chart.source)
    (s : Finset V2) (hs : s ∈ K.faces) :
    convexHull ℝ (s : Set V2) ⊆ C.left ∨ convexHull ℝ (s : Set V2) ⊆ C.right := by
  let A := convexHull ℝ (s : Set V2)
  have hAD : A ⊆ D2 := (K.convexHull_subset_space hs).trans hKD
  have hAi : (Subtype.val : D2 → V2) '' (Subtype.val ⁻¹' A) = A := by
    ext z
    exact ⟨fun ⟨u, hu, heq⟩ => heq ▸ hu, fun hz => ⟨⟨z, hAD hz⟩, hz, rfl⟩⟩
  have hconn : IsPreconnected ((Subtype.val : D2 → V2) ⁻¹' A) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hAi]
    exact (convex_convexHull ℝ _).isPreconnected
  have hcover : (Subtype.val : D2 → V2) ⁻¹' A ⊆
      Subtype.val ⁻¹' C.left ∪ Subtype.val ⁻¹' C.right := by
    intro z hz
    exact C.whole_preimage.subset ⟨z.property, hKC (K.convexHull_subset_space hs hz)⟩
  have hdis : Disjoint ((Subtype.val : D2 → V2) ⁻¹' C.left) (Subtype.val ⁻¹' C.right) :=
    C.disjoint.preimage Subtype.val
  rcases hconn.subset_or_subset C.left_open C.right_open hdis hcover with hL | hR
  · exact Or.inl (fun z hz => hL (a := ⟨z, hAD hz⟩) hz)
  · exact Or.inr (fun z hz => hR (a := ⟨z, hAD hz⟩) hz)



theorem RawCrossingChart.vertexSubcomplex_space
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X} {x y : V2}
    (C : RawCrossingChart e f R x y) (K : SimplicialComplex ℝ V2)
    (hKD : K.space ⊆ D2) (hKC : MapsTo f K.space C.chart.source) :
    (K.vertexSubcomplex C.left).space = K.space ∩ C.left ∧
    (K.vertexSubcomplex C.right).space = K.space ∩ C.right := by
  have hside (A B : Set V2) (hdis : Disjoint A B)
      (hfaces : ∀ s ∈ K.faces, convexHull ℝ (s : Set V2) ⊆ A ∨
        convexHull ℝ (s : Set V2) ⊆ B) : (K.vertexSubcomplex A).space = K.space ∩ A := by
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
      have hsA : convexHull ℝ (s : Set V2) ⊆ A :=
        (hfaces s hs).resolve_right (fun hB => disjoint_left.mp hdis hzA (hB hzs))
      exact SimplicialComplex.mem_space_iff.mpr ⟨s,
        ⟨hs, fun v hv => hsA (subset_convexHull ℝ _ hv)⟩, hzs⟩
  exact ⟨hside C.left C.right C.disjoint (C.face_in_one_branch K hKD hKC),
    hside C.right C.left C.disjoint.symm (fun s hs => (C.face_in_one_branch K hKD hKC s hs).symm)⟩

end PoincareConjecture.M76.Dehn
