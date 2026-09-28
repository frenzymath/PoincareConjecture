import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalLevels.Band

noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

def upperAbscissa (z : Real) : Real := (10 / 3) * (z^2 - z + 3 / 10)

def upperRadicand (z : Real) : Real := 1 - z^2 - (upperAbscissa z)^2

def upperLatitudePolynomial (z : Real) : Real := -100*z^3 + 200*z^2 - 169*z + 60

theorem upperRadicand_factor (z : Real) :
    upperRadicand z = (z / 9) * upperLatitudePolynomial z := by
  dsimp [upperRadicand, upperAbscissa, upperLatitudePolynomial]
  ring

theorem hasDerivAt_upperLatitudePolynomial (z : Real) :
    HasDerivAt upperLatitudePolynomial (-300*z^2 + 400*z - 169) z := by
  convert! (((((hasDerivAt_id z).pow 3).const_mul (-100 : Real)).add
    (((hasDerivAt_id z).pow 2).const_mul 200)).sub
    ((hasDerivAt_id z).const_mul 169)).add_const 60 using 1
  dsimp [upperLatitudePolynomial]
  ring

theorem strictAnti_upperLatitudePolynomial : StrictAnti upperLatitudePolynomial := by
  apply strictAnti_of_deriv_neg
  intro z
  rw [(hasDerivAt_upperLatitudePolynomial z).deriv]
  nlinarith [sq_nonneg (z - 2 / 3)]

theorem exists_upperLatitude_root :
    ∃ z : Real, 0 < z ∧ z < 1 ∧ upperLatitudePolynomial z = 0 := by
  have hc : Continuous upperLatitudePolynomial := by unfold upperLatitudePolynomial; fun_prop
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc' (by norm_num : (0 : Real) ≤ 1)
    hc.continuousOn (by norm_num [upperLatitudePolynomial] :
      (0 : Real) ∈ Icc (upperLatitudePolynomial 1) (upperLatitudePolynomial 0))
  have hl : 0 < z := by
    by_contra hh
    have hz0 : z = 0 := le_antisymm (le_of_not_gt hh) hz.1
    rw [hz0] at he
    norm_num [upperLatitudePolynomial] at he
  have hu : z < 1 := by
    by_contra hh
    have hz1 : z = 1 := le_antisymm hz.2 (le_of_not_gt hh)
    rw [hz1] at he
    norm_num [upperLatitudePolynomial] at he
  exact ⟨z, hl, hu, he⟩

def upperCutLatitude : Real := Classical.choose exists_upperLatitude_root

theorem upperCutLatitude_pos : 0 < upperCutLatitude :=
  (Classical.choose_spec exists_upperLatitude_root).1

theorem upperCutLatitude_lt_one : upperCutLatitude < 1 :=
  (Classical.choose_spec exists_upperLatitude_root).2.1

theorem upperLatitudePolynomial_upperCutLatitude : upperLatitudePolynomial upperCutLatitude = 0 :=
  (Classical.choose_spec exists_upperLatitude_root).2.2

theorem upperLatitudePolynomial_pos_iff (z : Real) :
    0 < upperLatitudePolynomial z ↔ z < upperCutLatitude := by
  rw [← upperLatitudePolynomial_upperCutLatitude, strictAnti_upperLatitudePolynomial.lt_iff_gt]

theorem upperLatitudePolynomial_neg_iff (z : Real) :
    upperLatitudePolynomial z < 0 ↔ upperCutLatitude < z := by
  rw [← upperLatitudePolynomial_upperCutLatitude, strictAnti_upperLatitudePolynomial.lt_iff_gt]

theorem upperRadicand_nonneg_iff (z : Real) :
    0 ≤ upperRadicand z ↔ z ∈ Icc 0 upperCutLatitude := by
  rw [upperRadicand_factor]
  constructor
  · intro hp
    have hz : 0 ≤ z := by
      by_contra hh
      have hn : z / 9 < 0 := by linarith
      have hc : 0 < upperLatitudePolynomial z :=
        (upperLatitudePolynomial_pos_iff z).mpr (by linarith [upperCutLatitude_pos])
      exact (not_lt_of_ge hp) (mul_neg_of_neg_of_pos hn hc)
    refine ⟨hz, ?_⟩
    by_contra hh
    have hn : 0 < z / 9 := by linarith [upperCutLatitude_pos]
    have hc : upperLatitudePolynomial z < 0 :=
      (upperLatitudePolynomial_neg_iff z).mpr (lt_of_not_ge hh)
    exact (not_lt_of_ge hp) (mul_neg_of_pos_of_neg hn hc)
  · intro hz
    apply mul_nonneg (by linarith [hz.1])
    rw [← upperLatitudePolynomial_upperCutLatitude]
    exact strictAnti_upperLatitudePolynomial.antitone hz.2

@[simp] theorem upperRadicand_zero : upperRadicand 0 = 0 := by
  rw [upperRadicand_factor]
  norm_num

@[simp] theorem upperRadicand_upperCutLatitude : upperRadicand upperCutLatitude = 0 := by
  rw [upperRadicand_factor, upperLatitudePolynomial_upperCutLatitude, mul_zero]

end Poincare.Manifold.Schoenflies.Saddle.Nested
