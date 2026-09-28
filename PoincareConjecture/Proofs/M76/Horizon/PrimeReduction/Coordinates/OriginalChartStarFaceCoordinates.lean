import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalEdgeCofaceCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_original_chart_star_face_coordinates
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X (Fin 3 → ℝ),
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g)) :
    ∃ (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X (Fin 3 → ℝ))
      (A : K.FaceOfCard 3 → E →ᴬ[ℝ] (Fin 3 → ℝ)),
      (∀ s i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      (∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source) ∧
      (∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E))) := by
  classical
  have hex (s : K.FaceOfCard 3) :
      ∃ (Q : OpenPartialHomeomorph X (Fin 3 → ℝ)) (A : E →ᴬ[ℝ] (Fin 3 → ℝ)),
        (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
        MapsTo g (convexHull ℝ (s.1 : Set E)) Q.source ∧
        EqOn (Q ∘ g) A (convexHull ℝ (s.1 : Set E)) := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < s.1.card by rw [s.2.2]; omega)
    obtain ⟨Q,hmap,hQ,hfaces⟩ := hstars p (K.face_subset_vertices s.2.1 hp)
    have hs : s.1 ∈ (K.closedStar p).faces :=
      ⟨s.2.1, by simpa only [Finset.insert_eq_of_mem hp] using s.2.1⟩
    obtain ⟨A,hA⟩ := hfaces s.1 hs
    exact ⟨Q,A,hQ,hmap.mono_left ((K.closedStar p).convexHull_subset_space hs),hA⟩
  choose Q A hQ hmap hA using hex
  exact ⟨Q,A,hQ,hmap,hA⟩

end PoincareConjecture.M76
