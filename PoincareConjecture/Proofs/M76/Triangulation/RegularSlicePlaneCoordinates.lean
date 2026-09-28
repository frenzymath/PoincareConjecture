import PoincareConjecture.Proofs.M76.Triangulation.RegularSliceCircles
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]




theorem exists_regularSlice_plane_polygons (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (a : (ℝ × ℝ) →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] (ℝ × ℝ))
    (hleft : Function.LeftInverse r a)
    (hright : LeftInvOn a r {x | A x = 0}) (ha : ∀ y, A (a y) = 0) :
    ∃ (n : (K.regularSliceGraph A).ConnectedComponent → ℕ)
      (Q : ∀ i, Polygon (ℝ × ℝ) (n i + 3)),
      (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges) ∧
      a ⁻¹' K.space = ⋃ i, (Q i).boundary ℝ ∧
      Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ)) := by
  obtain ⟨n, P, hP, hcover, hdisj⟩ :=
    K.exists_regularSlice_polygons A hK hreg hpure hcofaces
  have hbd (i) : (P i).boundary ℝ ⊆ K.space ∩ {x | A x = 0} := by
    rw [hcover]
    exact fun _ hx => mem_iUnion.mpr ⟨i, hx⟩
  have hPi (i) : LeftInvOn a r ((P i).boundary ℝ) := fun _ hx => hright (hbd i hx).2
  let Q := fun i => (P i).affineImage r.toAffineMap
  have hQ (i) : Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges ∧
      a '' (Q i).boundary ℝ = (P i).boundary ℝ :=
    (P i).affineImage_of_leftInvOn (hP i).2 (hP i).1 r.toAffineMap a.toAffineMap (hPi i)
  refine ⟨n, Q, fun i => ⟨(hQ i).1, (hQ i).2.1⟩, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ▸ (show a y ∈ K.space ∩ {x | A x = 0}
        from ⟨hy, ha y⟩))
      rw [← (hQ i).2.2] at hi
      exact mem_iUnion.mpr ⟨i, hleft.injective.mem_set_image.mp hi⟩
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact (hbd i ((hQ i).2.2 ▸ mem_image_of_mem a hi)).1
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    exact Set.disjoint_left.mp (hdisj hij)
      ((hQ i).2.2 ▸ mem_image_of_mem a hyi) ((hQ j).2.2 ▸ mem_image_of_mem a hyj)

end Geometry.SimplicialComplex
