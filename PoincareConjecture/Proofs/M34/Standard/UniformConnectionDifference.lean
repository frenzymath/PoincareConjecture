import PoincareConjecture.Proofs.M34.Standard.ConnectionDifferenceContinuity
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy

theorem exists_uniform_connectionDifference_bound
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {I0 : X → Inverse n} {gamma : X → Gamma n} {R1 : X → Raw n}
    {vp : X → Fin n → Fin n → V n}
    (hI : ContinuousOn I0 K) (hg : ContinuousOn gamma K)
    (hR : ContinuousOn R1 K) (hv : ContinuousOn vp K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ (d : Fin dS × Fin n → ℝ)
      (H : FH n) (A : FA n) (S : FS n) (ε : ℝ), 0 < ε →
        (∑ alpha : Fin dA, 2 * qA A alpha *
          qA (connectionDifferenceRate qS (I0 p) (gamma p) (R1 p) (vp p) d H A S) alpha) ≤
          ε * (∑ beta, d beta ^ 2) + (C / ε + C) *
            ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2)) := by
  let LD := fun p => (connectionEnergyCoordinates qA).comp
    (connectionDerivativeRate qS (I0 p))
  let LH := fun p => (connectionEnergyCoordinates qA).comp
    (connectionMetricRate (I0 p) (vp p))
  let LA := fun p => (connectionEnergyCoordinates qA).comp
    (connectionConnectionRate (I0 p) (R1 p))
  let LS := fun p => (connectionEnergyCoordinates qA).comp
    (connectionCurvatureRate (I0 p) (gamma p))
  have hcoord {f : X → FA n} (hf : ContinuousOn f K) (alpha : Fin dA) :
      ContinuousOn (fun p => connectionEnergyCoordinates qA (f p) alpha) K :=
    (EuclideanSpace.proj alpha).continuous.comp_continuousOn
      (qA.continuous.comp_continuousOn hf)
  obtain ⟨CD, hCD, hDbound⟩ := exists_compact_finite_linear_coordinate_bound hK LD
    (fun d alpha => hcoord (continuousOn_connectionDerivativeRate qS hI d) alpha)
  obtain ⟨CB, hCB, hBbound⟩ := exists_compact_three_linear_coordinate_bound hK qH qA qS
    LH LA LS
    (fun H alpha => hcoord (continuousOn_connectionMetricRate hI hv H) alpha)
    (fun A alpha => hcoord (continuousOn_connectionConnectionRate hI hR A) alpha)
    (fun S alpha => hcoord (continuousOn_connectionCurvatureRate hI hg S) alpha)
  let C := max CD (1 + CB)
  have hC : 0 ≤ C := hCD.trans (le_max_left _ _)
  refine ⟨C, hC, fun p hp d H A S ε hε => ?_⟩
  let rho := (∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2)
  have hrho : 0 ≤ rho := by dsimp only [rho]; positivity
  have ha : (∑ j, qA A j ^ 2) ≤ rho := by
    dsimp only [rho]
    have hh : 0 ≤ ∑ j, qH H j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hs : 0 ≤ ∑ j, qS S j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  have hd := (hDbound p hp d).2 ε hε (fun alpha => qA A alpha)
  have hb := (hBbound p hp H A S).2 1 zero_lt_one (fun alpha => qA A alpha)
  simp only [one_mul, div_one] at hb
  have hdiv : CD / ε ≤ C / ε := div_le_div_of_nonneg_right (le_max_left _ _) hε.le
  have h0 : CD / ε * (∑ j, qA A j ^ 2) ≤ C / ε * rho :=
    mul_le_mul hdiv ha (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (div_nonneg hC hε.le)
  have h1 : CB * (∑ j, qA A j ^ 2) ≤ CB * rho :=
    mul_le_mul_of_nonneg_left ha hCB
  have h2 : (1 + CB) * rho ≤ C * rho :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hrho
  simp only [connectionDifferenceRate, map_add, PiLp.add_apply]
  change (∑ alpha : Fin dA, 2 * qA A alpha *
    (LD p d alpha + LH p H alpha + LA p A alpha + LS p S alpha)) ≤
      ε * (∑ beta, d beta ^ 2) + (C / ε + C) * rho
  calc
    _ = (∑ alpha : Fin dA, 2 * qA A alpha * LD p d alpha) +
        ∑ alpha : Fin dA, 2 * qA A alpha *
          (LH p H alpha + LA p A alpha + LS p S alpha) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro alpha _
      ring
    _ ≤ ε * (∑ beta, d beta ^ 2) + CD / ε * (∑ j, qA A j ^ 2) +
        (rho + CB * (∑ j, qA A j ^ 2)) := add_le_add hd hb
    _ ≤ _ := by nlinarith only [h0, h1, h2]

end PoincareConjecture.M34.DifferenceEnergy
