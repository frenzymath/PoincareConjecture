import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.LeafAttachment
import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_triangle_affine_interpolation (p : Fin 3 → E)
    (hp : AffineIndependent ℝ p) (q : Fin 3 → F) :
    ∃ A : E →ᴬ[ℝ] F,
      (∀ i, A (p i) = q i) ∧
      A '' convexHull ℝ (range p) = convexHull ℝ (range q) ∧
      ∀ i j, A '' segment ℝ (p i) (p j) = segment ℝ (q i) (q j) := by
  classical
  let f : E → F := Function.extend p q (fun _ => 0)
  obtain ⟨A, hA⟩ := hp.range.exists_continuousAffineMap_eqOn f
  have hvertices (i : Fin 3) : A (p i) = q i := by
    rw [hA (mem_range_self i)]
    exact hp.injective.extend_apply q (fun _ => 0) i
  refine ⟨A, hvertices, ?_, ?_⟩
  · calc
      _ = convexHull ℝ (A '' range p) := A.toAffineMap.image_convexHull _
      _ = _ := by
        congr 1
        ext x
        simp only [mem_image, mem_range, exists_exists_eq_and]
        simp only [hvertices]
  · intro i j
    calc
      _ = segment ℝ (A (p i)) (A (p j)) := image_segment ℝ A.toAffineMap _ _
      _ = _ := by rw [hvertices, hvertices]

variable [FiniteDimensional ℝ F]

theorem exists_triangle_affine_inverse (p : Fin 3 → E) (q : Fin 3 → F)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) :
    ∃ (A : E →ᴬ[ℝ] F) (B : F →ᴬ[ℝ] E),
      (∀ i, A (p i) = q i) ∧ (∀ i, B (q i) = p i) ∧
      LeftInvOn B A (convexHull ℝ (range p)) ∧
      LeftInvOn A B (convexHull ℝ (range q)) ∧
      A '' convexHull ℝ (range p) = convexHull ℝ (range q) ∧
      InjOn A (convexHull ℝ (range p)) ∧
      ∀ i j, A '' segment ℝ (p i) (p j) = segment ℝ (q i) (q j) := by
  obtain ⟨A, hA, himage, hedge⟩ := exists_triangle_affine_interpolation p hp q
  obtain ⟨B, hB, _, _⟩ := exists_triangle_affine_interpolation q hq p
  have hleft : LeftInvOn B A (convexHull ℝ (range p)) := by
    have hvertices : EqOn (B.toAffineMap.comp A.toAffineMap) (AffineMap.id ℝ E)
        (range p) := by
      rintro x ⟨i, rfl⟩
      change B (A (p i)) = p i
      rw [hA, hB]
    exact fun _ hx => AffineMap.eqOn_affineSpan hvertices (convexHull_subset_affineSpan _ hx)
  have hright : LeftInvOn A B (convexHull ℝ (range q)) := by
    have hvertices : EqOn (A.toAffineMap.comp B.toAffineMap) (AffineMap.id ℝ F)
        (range q) := by
      rintro x ⟨i, rfl⟩
      change A (B (q i)) = q i
      rw [hB, hA]
    exact fun _ hx => AffineMap.eqOn_affineSpan hvertices (convexHull_subset_affineSpan _ hx)
  exact ⟨A, B, hA, hB, hleft, hright, himage, hleft.injOn, hedge⟩

def triangleRim (p : Fin 3 → E) : Set E :=
  segment ℝ (p 0) (p 1) ∪ segment ℝ (p 1) (p 2) ∪ segment ℝ (p 2) (p 0)

omit [FiniteDimensional ℝ E] in
theorem triangle_interpolation_frontier (p : Fin 3 → E)
    (A : (ℝ × ℝ) →ᴬ[ℝ] E) (hA : ∀ i, A (rightTriangle i) = p i) :
    A '' frontier (convexHull ℝ (range rightTriangle)) = triangleRim p := by
  have hfrontier : frontier (convexHull ℝ (range rightTriangle)) =
      segment ℝ (rightTriangle 0) (rightTriangle 1) ∪
        segment ℝ (rightTriangle 1) (rightTriangle 2) ∪
        segment ℝ (rightTriangle 2) (rightTriangle 0) := by
    rw [rightTriangle.frontier_convexHull_triangle independent_rightTriangle]
    ext x
    simp [Polygon.boundary, Polygon.edgeSet, rightTriangle, Fin.exists_fin_succ,
      affineSegment_eq_segment, or_assoc]
  rw [hfrontier, image_union, image_union]
  have himage (i j : Fin 3) : A '' segment ℝ (rightTriangle i) (rightTriangle j) =
      segment ℝ (p i) (p j) := by
    calc
      _ = segment ℝ (A (rightTriangle i)) (A (rightTriangle j)) :=
        image_segment ℝ A.toAffineMap _ _
      _ = _ := by rw [hA, hA]
  simp only [himage, triangleRim]

theorem isFinitePLBallPair_triangleRim (p : Fin 3 → E)
    (hp : AffineIndependent ℝ p) :
    IsFinitePLBallPair (ℝ × ℝ) (convexHull ℝ (range p)) (triangleRim p) := by
  obtain ⟨A, B, hA, hB, hleft, hright, himage, hinj, hedge⟩ :=
    exists_triangle_affine_inverse rightTriangle p independent_rightTriangle hp
  have h := (rightTriangle.isFinitePLBallPair_convexHull_triangle
    independent_rightTriangle).affine_image A hinj
  rwa [himage, triangle_interpolation_frontier p A hA] at h

theorem exists_original_triangle_disk (K : SimplicialComplex ℝ E) (s : Triangle K) :
    ∃ p : Fin 3 → E, range p = (s.val : Set E) ∧ AffineIndependent ℝ p ∧
      IsFinitePLBallPair (ℝ × ℝ) (convexHull ℝ (s.val : Set E)) (triangleRim p) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp s.property.2
  let p : Fin 3 → E := ![a, b, c]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  have hrange : range p = (s.val : Set E) := by
    rw [hs]
    ext x
    simp [p, eq_comm, or_comm, or_left_comm]
  have hind : AffineIndependent ℝ p :=
    ((K.indep s.property.1).mono hrange.subset).of_set_of_injective hp
  refine ⟨p, hrange, hind, ?_⟩
  rw [← hrange]
  exact isFinitePLBallPair_triangleRim p hind

end PoincareConjecture.M76.OriginalTriangleCopies
