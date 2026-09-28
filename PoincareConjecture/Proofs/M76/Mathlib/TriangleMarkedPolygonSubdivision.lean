import PoincareConjecture.Proofs.M76.Mathlib.ConnectedTriangleSections
import PoincareConjecture.Proofs.M76.Mathlib.FiniteMarkedPolygonSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.PolygonInteriorCutArcs










set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}




theorem open_edge_subset_original_triangle (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) (c : ℝ)
    (hsection : P.boundary ℝ ⊆ K.space ∩ {x | A x = c})
    (hmarks : K.oneSkeletonHeightSection A c ∩ P.boundary ℝ ⊆ range P)
    (i : Fin (n + 3)) :
    ∃ s ∈ K.faces, s.card = 3 ∧
      AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) '' Ioo (0 : ℝ) 1 ⊆
        intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  let T := AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) '' Ioo (0 : ℝ) 1
  have hT : IsConnected T :=
    (isConnected_Ioo (show (0 : ℝ) < 1 from zero_lt_one)).image _
      AffineMap.lineMap_continuous.continuousOn
  have hTP : T ⊆ P.boundary ℝ := by
    rintro x ⟨r, hr, rfl⟩
    exact mem_iUnion.mpr ⟨i, r, ⟨hr.1.le, hr.2.le⟩, rfl⟩
  apply K.exists_triangle_containing_connected_height_section hK hpure A c hT
    (hTP.trans hsection)
  apply disjoint_left.mpr
  rintro x ⟨r, hr, rfl⟩ hx
  exact P.edgeCut_notMem_range hP hinj (fun _ => r) hr
    (hmarks ⟨hx, hTP ⟨r, hr, rfl⟩⟩)






theorem exists_subdivision_with_original_triangle_edges (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) (c : ℝ)
    (hsection : P.boundary ℝ ⊆ K.space ∩ {x | A x = c}) :
    ∃ (M : ℕ) (Q : Polygon E (M + 3)), Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      range P ∪ (K.oneSkeletonHeightSection A c ∩ P.boundary ℝ) ⊆ range Q ∧
      ∀ i, ∃ s ∈ K.faces, s.card = 3 ∧
        AffineMap.lineMap (Q i) (Q (finRotate (M + 3) i)) '' Ioo (0 : ℝ) 1 ⊆
          intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  have hF : (K.oneSkeletonHeightSection A c ∩ P.boundary ℝ).Finite :=
    (K.finite_oneSkeletonHeightSection hK A hA c).subset inter_subset_left
  obtain ⟨M, Q, hQ, hQi, hQP, hretain⟩ :=
    P.exists_subdivision_at_finite_marks hP hinj hF inter_subset_right
  have hQsection : Q.boundary ℝ ⊆ K.space ∩ {x | A x = c} := by
    rw [hQP]
    exact hsection
  have hQmarks : K.oneSkeletonHeightSection A c ∩ Q.boundary ℝ ⊆ range Q := by
    intro x hx
    exact hretain (Or.inr ⟨hx.1, hQP ▸ hx.2⟩)
  exact ⟨M, Q, hQ, hQi, hQP, hretain,
    Q.open_edge_subset_original_triangle hQ hQi K hK hpure A c hQsection hQmarks⟩

end Polygon
