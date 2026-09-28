import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators
import PoincareConjecture.Proofs.M76.Mathlib.RadialEmbeddingNormalization
import PoincareConjecture.Proofs.M76.Smoothing.PlanarCircleEdges

set_option autoImplicit false

open Set Geometry NormedSpace

namespace PoincareConjecture.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

noncomputable def planarGapEdgeVertices (w : shortArcGapSpace n theta)
    (i : Fin (n + 3)) : Finset ℂ := by
  classical
  exact {planarGapVertices w i, planarGapVertices w (i + 1)}

private theorem planar_generators_independent (w : shortArcGapSpace n theta) :
    ∀ s ∈ range (planarGapEdgeVertices w), AffineIndependent ℝ ((↑) : s → ℂ) := by
  rintro _ ⟨i, rfl⟩
  have h := (linearIndependent_planarGapEdge w i).affineIndependent
  have he : (planarGapEdgeVertices w i : Set ℂ) =
      {planarGapVertices w i, planarGapVertices w (i + 1)} := by
    simp only [planarGapEdgeVertices, Finset.coe_pair]
  rw [← he] at h
  exact h

private theorem planar_generators_inter (w : shortArcGapSpace n theta) :
    ∀ s ∈ range (planarGapEdgeVertices w), ∀ t ∈ range (planarGapEdgeVertices w),
      convexHull ℝ (s : Set ℂ) ∩ convexHull ℝ (t : Set ℂ) ⊆
        convexHull ℝ ((s : Set ℂ) ∩ t) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  simpa only [planarGapEdgeVertices, Finset.coe_pair, convexHull_pair, planarGapEdge] using
    planarGapEdge_inter_subset w i j

noncomputable def planarCircleComplex (w : shortArcGapSpace n theta) : SimplicialComplex ℝ ℂ :=
  SimplicialComplex.ofGenerators (range (planarGapEdgeVertices w))
    (planar_generators_independent w) (planar_generators_inter w)

theorem mem_planarCircleComplex_faces (w : shortArcGapSpace n theta) (s : Finset ℂ) :
    s ∈ (planarCircleComplex w).faces ↔ s.Nonempty ∧ ∃ i, s ⊆ planarGapEdgeVertices w i := by
  change (s.Nonempty ∧ ∃ t ∈ range (planarGapEdgeVertices w), s ⊆ t) ↔ _
  constructor
  · rintro ⟨hs, _, ⟨i, rfl⟩, hsi⟩
    exact ⟨hs, i, hsi⟩
  · rintro ⟨hs, i, hsi⟩
    exact ⟨hs, _, mem_range_self i, hsi⟩

theorem finite_planarCircleComplex_faces (w : shortArcGapSpace n theta) :
    (planarCircleComplex w).faces.Finite :=
  SimplicialComplex.finite_ofGenerators_faces (finite_range _) _ _

theorem planarCircleComplex_space (w : shortArcGapSpace n theta) :
    (planarCircleComplex w).space = ⋃ i, planarGapEdge w i := by
  rw [planarCircleComplex, SimplicialComplex.space_ofGenerators]
  ext x
  constructor
  · intro hx
    obtain ⟨_, ⟨i, rfl⟩, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨i, by
      simpa only [planarGapEdgeVertices, Finset.coe_pair, convexHull_pair, planarGapEdge]
        using hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    refine mem_iUnion₂.mpr ⟨_, mem_range_self i, ?_⟩
    simpa only [planarGapEdgeVertices, Finset.coe_pair, convexHull_pair, planarGapEdge] using hxi

theorem linearIndependent_planarCircleComplex_face (w : shortArcGapSpace n theta)
    {s : Finset ℂ} (hs : s ∈ (planarCircleComplex w).faces) :
    LinearIndependent ℝ ((↑) : s → ℂ) := by
  obtain ⟨_, i, hsi⟩ := (mem_planarCircleComplex_faces w s).mp hs
  change LinearIndepOn ℝ id (s : Set ℂ)
  have hi : LinearIndepOn ℝ id
      ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) :=
    linearIndependent_planarGapEdge w i
  apply hi.mono
  change (s : Set ℂ) ⊆ (planarGapEdgeVertices w i : Set ℂ) at hsi
  simpa only [planarGapEdgeVertices, Finset.coe_pair] using hsi

theorem injOn_normalize_planarCircleComplex (w : shortArcGapSpace n theta) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (planarCircleComplex w).space := by
  rw [planarCircleComplex_space]
  exact injOn_normalize_iUnion_planarGapEdge w

theorem normalize_image_planarCircleComplex (w : shortArcGapSpace n theta) :
    NormedSpace.normalize '' (planarCircleComplex w).space = Metric.sphere (0 : ℂ) 1 := by
  rw [planarCircleComplex_space]
  exact normalize_image_iUnion_planarGapEdge w

def cyclicEdgeComplex (n : ℕ) : AbstractSimplicialComplex (Fin (n + 3)) where
  faces := {s | s.Nonempty ∧ ∃ i, s ⊆ {i, i + 1}}
  isRelLowerSet_faces := by
    rintro s ⟨hs, i, hsi⟩
    exact ⟨hs, fun t hts ht => ⟨ht, i, hts.trans hsi⟩⟩
  singleton_mem i := ⟨Finset.singleton_nonempty i, i, by simp⟩

theorem planarCircleComplex_faces_image (w : shortArcGapSpace n theta) :
    (planarCircleComplex w).faces =
      {t : Finset ℂ | ∃ s ∈ (cyclicEdgeComplex n).faces,
        (t : Set ℂ) = planarGapVertices w '' (s : Set (Fin (n + 3)))} := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨hne, i, hti⟩ := (mem_planarCircleComplex_faces w t).mp ht
    have hsub : t ⊆ ({i, i + 1} : Finset (Fin (n + 3))).image (planarGapVertices w) := by
      simpa only [Finset.image_insert, Finset.image_singleton, planarGapEdgeVertices] using hti
    obtain ⟨s, hsi, rfl⟩ := Finset.subset_image_iff.mp hsub
    exact ⟨s, ⟨Finset.image_nonempty.mp hne, i, hsi⟩, Finset.coe_image⟩
  · rintro ⟨s, ⟨hs, i, hsi⟩, hts⟩
    have ht : t = s.image (planarGapVertices w) :=
      Finset.coe_injective (hts.trans Finset.coe_image.symm)
    rw [ht, mem_planarCircleComplex_faces]
    refine ⟨Finset.image_nonempty.mpr hs, i, ?_⟩
    simpa only [Finset.image_insert, Finset.image_singleton, planarGapEdgeVertices] using
      Finset.image_subset_image (f := planarGapVertices w) hsi

theorem isRadialEmbedding_planarGapVertices (w : shortArcGapSpace n theta) :
    (cyclicEdgeComplex n).IsRadialEmbedding (planarGapVertices w) :=
  ⟨injective_planarGapVertices w, planarCircleComplex w, planarCircleComplex_faces_image w,
    fun _ hs => linearIndependent_planarCircleComplex_face w hs,
    injOn_normalize_planarCircleComplex w⟩

noncomputable def planarGapEmbedding (w : shortArcGapSpace n theta) :
    (cyclicEdgeComplex n).UnitRadialEmbedding ℂ :=
  ⟨⟨planarGapVertices w, isRadialEmbedding_planarGapVertices w⟩, norm_planarGapVertices w⟩

theorem continuous_planarGapEmbedding :
    Continuous (planarGapEmbedding : shortArcGapSpace n theta →
      (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) :=
  (continuous_planarGapVertices.subtype_mk _).subtype_mk _

end PoincareConjecture.M76.Smoothing
