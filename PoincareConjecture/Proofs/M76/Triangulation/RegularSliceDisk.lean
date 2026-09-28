import PoincareConjecture.Proofs.M76.Triangulation.RegularSlicePlaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AffineInnermostDisk

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_regularSlice_finitePL_disk (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (a : (ℝ × ℝ) →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] (ℝ × ℝ))
    (hleft : Function.LeftInverse r a)
    (hright : LeftInvOn a r {x | A x = 0}) (ha : ∀ y, A (a y) = 0)
    (hne : (K.space ∩ {x | A x = 0}).Nonempty) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)) (D : Set E),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧
      D ⊆ {x | A x = 0} ∧ D ∩ K.space = P.boundary ℝ ∧
      Disjoint (D \ P.boundary ℝ) K.space := by
  classical
  obtain ⟨n, Q, hQ, hsection, hdisj⟩ := K.exists_regularSlice_plane_polygons A
    hK hreg hpure hcofaces a r hleft hright ha
  let := K.finite_regularSliceGraph_components A hK
  obtain ⟨x, hx⟩ := hne
  have hy : r x ∈ a ⁻¹' K.space := by
    change a (r x) ∈ K.space
    rw [hright hx.2]
    exact hx.1
  obtain ⟨i, _⟩ := mem_iUnion.mp (hsection ▸ hy)
  let : Nonempty (K.regularSliceGraph A).ConnectedComponent := ⟨i⟩
  obtain ⟨j, hdisk, hinter, _⟩ := Polygon.exists_innermost_affine_disk n Q
    (fun i => (hQ i).2) (fun i => (hQ i).1) hdisj a hleft.injective K.space hsection
  let P := (Q j).affineImage a.toAffineMap
  have hPbd : P.boundary ℝ = a '' (Q j).boundary ℝ := (Q j).affineImage_boundary a.toAffineMap
  rw [← hPbd] at hdisk hinter
  refine ⟨n j, P, a '' closure (Q j).inside,
    hleft.injective.comp (hQ j).1,
    (Q j).hasSimplicialEdges_affineImage_of_injOn (hQ j).2 a.toAffineMap hleft.injective.injOn,
    hdisk, ?_, hinter, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact ha y
  · exact Set.disjoint_left.mpr fun x hx hxK => hx.2 (hinter ▸ And.intro hx.1 hxK)

end Geometry.SimplicialComplex
