import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryFamilies
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPresentation










set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]




theorem hasAlexanderCurvePresentation_zero_of_disjoint_family
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {s r : Set E} (hr : r.Subsingleton) (hcover : s = r ∪ ⋃ i, (P i).boundary ℝ) :
    HasAlexanderCurvePresentation s 0 := by
  have hc := (alexanderCurveCount_eq_zero_iff (fun i => (P i).boundary ℝ)).mpr hpair
  rw [← hc]
  apply hasAlexanderCurvePresentation_of_family n P hP hr hcover
  intro i j hij
  rw [(hpair hij).inter_eq]
  exact empty_subset r



theorem hasAlexanderCurvePresentation_zero_union_polygon
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {s : Set E} (hcover : s = ⋃ i, (P i).boundary ℝ)
    {m : ℕ} (Q : Polygon E (m + 3)) (hQi : Function.Injective Q)
    (hQe : Q.HasSimplicialEdges) (hsep : Disjoint (Q.boundary ℝ) s) :
    HasAlexanderCurvePresentation (Q.boundary ℝ ∪ s) 0 := by
  let N : Option ι → ℕ
    | none => m
    | some i => n i
  let R : ∀ i, Polygon E (N i + 3)
    | none => Q
    | some i => P i
  have hR (i : Option ι) : Function.Injective (R i) ∧ (R i).HasSimplicialEdges := by
    cases i with
    | none => exact ⟨hQi, hQe⟩
    | some i => exact hP i
  have hPs (i : ι) : (P i).boundary ℝ ⊆ s := by
    rw [hcover]
    exact subset_iUnion (fun i => (P i).boundary ℝ) i
  have hRpair : Pairwise (fun i j => Disjoint ((R i).boundary ℝ) ((R j).boundary ℝ)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hsep.mono_right (hPs j)
    | some i =>
      cases j with
      | none => exact (hsep.mono_right (hPs i)).symm
      | some j => exact hpair (fun h => hij (congrArg some h))
  apply hasAlexanderCurvePresentation_zero_of_disjoint_family N R hR hRpair
    (r := ∅) subsingleton_empty
  rw [empty_union, iUnion_option, hcover]




theorem hasAlexanderCurvePresentation_zero_union_cap [FiniteDimensional ℝ E]
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {s cap : Set E} (hcover : s = ⋃ i, (P i).boundary ℝ)
    (hcap : cap.Subsingleton ∨ ∃ d : Set E, IsFinitePLBallPair (ℝ × ℝ) d cap)
    (hsep : Disjoint cap s) : HasAlexanderCurvePresentation (cap ∪ s) 0 := by
  rcases hcap with hcap | ⟨d, hd⟩
  · exact hasAlexanderCurvePresentation_zero_of_disjoint_family n P hP hpair hcap
      (congrArg (cap ∪ ·) hcover)
  · obtain ⟨m, Q, hQi, hQe, hQb⟩ := hd.exists_polygon_boundary
    rw [← hQb] at hsep ⊢
    exact hasAlexanderCurvePresentation_zero_union_polygon n P hP hpair hcover Q hQi hQe hsep





theorem hasAlexanderCurvePresentation_zero_of_ordinary_level
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {b X : Set E} {cap Y : Set F} (hb : IsClosed b)
    (hsep : Disjoint b X) (hcover : b ∪ X = ⋃ i, (P i).boundary ℝ)
    (e : X ≃ₜ Y) (he : e.IsFinitePL)
    (hcap : cap.Subsingleton ∨ ∃ d : Set F, IsFinitePLBallPair (ℝ × ℝ) d cap)
    (hcapSep : Disjoint cap Y) : HasAlexanderCurvePresentation (cap ∪ Y) 0 := by
  obtain ⟨I, N, Q, hQ, hY, hQpair⟩ :=
    Polygon.exists_disjoint_finitePL_remainder_family n P
      (fun i => (hP i).2) (fun i => (hP i).1) hpair hb hsep hcover e he
  exact hasAlexanderCurvePresentation_zero_union_cap N Q hQ hQpair hY hcap hcapSep

end Set
