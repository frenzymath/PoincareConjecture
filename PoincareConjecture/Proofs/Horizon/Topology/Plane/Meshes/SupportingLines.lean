import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Subdivision.Lines

set_option autoImplicit false
open Set

namespace Poincare.Topology.Plane.Meshes

theorem triangle_inter_zero_subset_edge_of_nonneg
    (b : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (hsurj : Function.Surjective l) (hpos : ∀ i, 0 ≤ l (b i)) :
    ∃ i : Fin 3, convexHull ℝ (range b) ∩ {z | l z = 0} ⊆
      affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
  classical
  have hnonzero : ∃ i, l (b i) ≠ 0 := by
    by_contra! hzero
    have heq : l = 0 := AffineMap.ext_on b.tot (by
      rintro p ⟨i, rfl⟩
      exact hzero i)
    obtain ⟨p, hp⟩ := hsurj 1
    simp [heq] at hp
  obtain ⟨i, hi⟩ := hnonzero
  refine ⟨i, ?_⟩
  rw [convexHull_inter_affine_zero_of_nonneg_set (range b) l
    (by rintro p ⟨j, rfl⟩; exact hpos j), affineSegment_eq_segment, ← convexHull_pair]
  apply convexHull_mono
  rintro p ⟨⟨j, rfl⟩, hj⟩
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  fin_cases i <;> fin_cases j <;> simp_all [Fin.succAbove, Fin.lt_def, Fin.ext_iff]

theorem triangle_inter_zero_subset_edge
    (b : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (hsurj : Function.Surjective l)
    (hside : (∀ i, 0 ≤ l (b i)) ∨ (∀ i, l (b i) ≤ 0)) :
    ∃ i : Fin 3, convexHull ℝ (range b) ∩ {z | l z = 0} ⊆
      affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
  rcases hside with hpos | hneg
  · exact triangle_inter_zero_subset_edge_of_nonneg b l hsurj hpos
  · have hsurjneg : Function.Surjective (-l) := by
      intro t
      obtain ⟨p, hp⟩ := hsurj (-t)
      exact ⟨p, by simpa using congrArg Neg.neg hp⟩
    have hzero : {z | (-l) z = 0} = {z | l z = 0} := by
      ext z
      change -l z = 0 ↔ l z = 0
      exact neg_eq_zero
    simpa only [hzero] using
      triangle_inter_zero_subset_edge_of_nonneg b (-l) hsurjneg
        (fun i => by simpa using neg_nonneg.mpr (hneg i))

end Poincare.Topology.Plane.Meshes
