import PoincareConjecture.Proofs.M34.Standard.CoordinateTransportDensity











set_option autoImplicit false

set_option maxSynthPendingDepth 8

open scoped BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_reverse_coordinate_transport_density_bound {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {m : ℝ} (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : V n →L[ℝ] V n), L.IsInvertible → ‖L‖ ≤ m → ‖L.inverse‖ ≤ m →
      ∀ (H H' : FH n) (A A' : FA n) (S S' : FS n),
        (∀ u v, H u v = H' (L u) (L v)) →
        (∀ u v, A u v = L.inverse (A' (L u) (L v))) →
        (∀ u v w, S u v w = L.inverse (S' (L u) (L v) (L w))) →
        (∑ i, qH H' i ^ 2) + (∑ i, qA A' i ^ 2) + (∑ i, qS S' i ^ 2) ≤
          C * ((∑ i, qH H i ^ 2) + (∑ i, qA A i ^ 2) + (∑ i, qS S i ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_coordinate_transport_density_bound qH qA qS hm
  refine ⟨C, hC, ?_⟩
  intro L hi hL hLi H H' A A' S S' hH hA hS
  apply hbound L.inverse hLi (by rwa [hi.inverse_inverse]) H' H A' A S' S
  · intro u v
    simpa only [hi.self_apply_inverse] using (hH (L.inverse u) (L.inverse v)).symm
  · intro u v
    simp only [hi.inverse_inverse, hA, hi.self_apply_inverse]
  · intro u v w
    simp only [hi.inverse_inverse, hS, hi.self_apply_inverse]

end PoincareConjecture.M34
