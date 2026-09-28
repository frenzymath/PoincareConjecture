import PoincareConjecture.Proofs.M34.Mathlib.TensorTransportNorm
import PoincareConjecture.Proofs.M34.Standard.DifferenceFluxAlgebra

set_option autoImplicit false

set_option maxSynthPendingDepth 8

open scoped BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem exists_coordinate_transport_density_bound {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {m : ℝ} (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : V n →L[ℝ] V n), ‖L‖ ≤ m → ‖L.inverse‖ ≤ m →
      ∀ (H H' : FH n) (A A' : FA n) (S S' : FS n),
        (∀ u v, H u v = H' (L u) (L v)) →
        (∀ u v, A u v = L.inverse (A' (L u) (L v))) →
        (∀ u v w, S u v w = L.inverse (S' (L u) (L v) (L w))) →
        (∑ i, qH H i ^ 2) + (∑ i, qA A i ^ 2) + (∑ i, qS S i ^ 2) ≤
          C * ((∑ i, qH H' i ^ 2) + (∑ i, qA A' i ^ 2) + (∑ i, qS S' i ^ 2)) := by
  let cH := ‖qH.toContinuousLinearMap‖ * m ^ 2 * ‖qH.symm.toContinuousLinearMap‖
  let cA := ‖qA.toContinuousLinearMap‖ * m ^ 3 * ‖qA.symm.toContinuousLinearMap‖
  let cS := ‖qS.toContinuousLinearMap‖ * m ^ 4 * ‖qS.symm.toContinuousLinearMap‖
  let C := cH ^ 2 + cA ^ 2 + cS ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro L hL hLi H H' A A' S S' hH hA hS
  have hHb : ‖H‖ ≤ m ^ 2 * ‖H'‖ := by
    have hh := ContinuousLinearMap.norm_bilinear_transport_le L
      (ContinuousLinearMap.id ℝ ℝ) H H' hH
    simp only [ContinuousLinearMap.norm_id, one_mul] at hh
    calc
      ‖H‖ ≤ ‖H'‖ * ‖L‖ ^ 2 := hh
      _ ≤ ‖H'‖ * m ^ 2 := by gcongr
      _ = m ^ 2 * ‖H'‖ := by ring
  have hAb : ‖A‖ ≤ m ^ 3 * ‖A'‖ := by
    calc
      ‖A‖ ≤ ‖L.inverse‖ * ‖A'‖ * ‖L‖ ^ 2 :=
        ContinuousLinearMap.norm_bilinear_transport_le L L.inverse A A' hA
      _ ≤ m * ‖A'‖ * m ^ 2 := by gcongr
      _ = m ^ 3 * ‖A'‖ := by ring
  have hSb : ‖S‖ ≤ m ^ 4 * ‖S'‖ := by
    calc
      ‖S‖ ≤ ‖L.inverse‖ * ‖S'‖ * ‖L‖ ^ 3 :=
        ContinuousLinearMap.norm_trilinear_transport_le L L.inverse S S' hS
      _ ≤ m * ‖S'‖ * m ^ 3 := by gcongr
      _ = m ^ 4 * ‖S'‖ := by ring
  have hcoord {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] {d : ℕ}
      (q : T ≃L[ℝ] EuclideanSpace ℝ (Fin d)) {X Y : T} {b : ℝ}
      (hb : 0 ≤ b) (hXY : ‖X‖ ≤ b * ‖Y‖) :
      ‖q X‖ ≤ (‖q.toContinuousLinearMap‖ * b * ‖q.symm.toContinuousLinearMap‖) * ‖q Y‖ := by
    have hY : ‖Y‖ ≤ ‖q.symm.toContinuousLinearMap‖ * ‖q Y‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
        q.symm.toContinuousLinearMap.le_opNorm (q Y)
    calc
      ‖q X‖ ≤ ‖q.toContinuousLinearMap‖ * ‖X‖ := q.toContinuousLinearMap.le_opNorm X
      _ ≤ ‖q.toContinuousLinearMap‖ * (b * ‖Y‖) := by gcongr
      _ ≤ ‖q.toContinuousLinearMap‖ * (b * (‖q.symm.toContinuousLinearMap‖ * ‖q Y‖)) := by
        gcongr
      _ = _ := by ring
  have hqH : ‖qH H‖ ≤ cH * ‖qH H'‖ := hcoord qH (by positivity) hHb
  have hqA : ‖qA A‖ ≤ cA * ‖qA A'‖ := hcoord qA (by positivity) hAb
  have hqS : ‖qS S‖ ≤ cS * ‖qS S'‖ := hcoord qS (by positivity) hSb
  have hsq {a b c : ℝ} (ha : 0 ≤ a)
      (hab : a ≤ c * b) (hcC : c ^ 2 ≤ C) : a ^ 2 ≤ C * b ^ 2 := by
    have hh := pow_le_pow_left₀ ha hab 2
    rw [mul_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcC (sq_nonneg b))
  have hCH : cH ^ 2 ≤ C := (le_add_of_nonneg_right (sq_nonneg cA)).trans
    (le_add_of_nonneg_right (sq_nonneg cS))
  have hCA : cA ^ 2 ≤ C := (le_add_of_nonneg_left (sq_nonneg cH)).trans
    (le_add_of_nonneg_right (sq_nonneg cS))
  have hCS : cS ^ 2 ≤ C := le_add_of_nonneg_left (add_nonneg (sq_nonneg cH) (sq_nonneg cA))
  have hsH := hsq (norm_nonneg _) hqH hCH
  have hsA := hsq (norm_nonneg _) hqA hCA
  have hsS := hsq (norm_nonneg _) hqS hCS
  rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq,
    ← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq,
    ← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  simpa only [mul_add] using add_le_add (add_le_add hsH hsA) hsS

end PoincareConjecture.M34
