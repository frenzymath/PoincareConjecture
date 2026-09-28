import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.PrincipalHessianBound
open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

theorem integral_timeDeriv_mul_spatialSecond_eq_neg
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (i j : Fin n) :
    (∫ z, timeDeriv v z * spatialSecond i j v z) =
      -(∫ z, spatialDeriv i (timeDeriv v) z * spatialDeriv j v z) := by
  have h := integral_directionalDeriv_mul_eq_neg
    (f := spatialDeriv j v) (g := timeDeriv v)
    (contDiff_spatialDeriv hv j) (hasCompactSupport_spatialDeriv j hvc)
    (contDiff_timeDeriv hv) (hasCompactSupport_timeDeriv hvc)
    (spatialDirection i)
  simpa [spatialSecond, spatialDeriv, timeDeriv, mul_comm] using h

theorem integral_timeDeriv_mul_spatialSecond_pair_zero
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (i j : Fin n) :
    (∫ z, timeDeriv v z * spatialSecond i j v z) +
      (∫ z, timeDeriv v z * spatialSecond j i v z) = 0 := by
  have hij := integral_timeDeriv_mul_spatialSecond_eq_neg hv hvc i j
  have hji := integral_timeDeriv_mul_spatialSecond_eq_neg hv hvc j i
  have hprod := integral_directionalDeriv_mul_eq_neg
    (f := spatialDeriv i v) (g := spatialDeriv j v)
    (contDiff_spatialDeriv hv i) (hasCompactSupport_spatialDeriv i hvc)
    (contDiff_spatialDeriv hv j) (hasCompactSupport_spatialDeriv j hvc)
    (0, 1)
  have hleft : (fun z => fderiv ℝ (spatialDeriv i v) z (0, 1)) =
      (fun z => spatialDeriv i (timeDeriv v) z) := by
    funext z
    change fderiv ℝ (fun y => fderiv ℝ v y (spatialDirection i)) z (0, 1) =
      fderiv ℝ (fun y => fderiv ℝ v y (0, 1)) z (spatialDirection i)
    exact directionalSecond_comm v hv (0, 1) (spatialDirection i) z
  have hright : (fun z => fderiv ℝ (spatialDeriv j v) z (0, 1)) =
      (fun z => spatialDeriv j (timeDeriv v) z) := by
    funext z
    change fderiv ℝ (fun y => fderiv ℝ v y (spatialDirection j)) z (0, 1) =
      fderiv ℝ (fun y => fderiv ℝ v y (0, 1)) z (spatialDirection j)
    exact directionalSecond_comm v hv (0, 1) (spatialDirection j) z
  have hprod' :
      (∫ z, spatialDeriv i (timeDeriv v) z * spatialDeriv j v z) =
        -(∫ z, spatialDeriv i v z * spatialDeriv j (timeDeriv v) z) := by
    calc
      (∫ z, spatialDeriv i (timeDeriv v) z * spatialDeriv j v z) =
          ∫ z, fderiv ℝ (spatialDeriv i v) z (0, 1) * spatialDeriv j v z := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [congrFun hleft z]
      _ = -(∫ z, spatialDeriv i v z * fderiv ℝ (spatialDeriv j v) z (0, 1)) := hprod
      _ = -(∫ z, spatialDeriv i v z * spatialDeriv j (timeDeriv v) z) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with z
        rw [congrFun hright z]
  have hprod'' :
      (∫ z, spatialDeriv i (timeDeriv v) z * spatialDeriv j v z) =
        -(∫ z, spatialDeriv j (timeDeriv v) z * spatialDeriv i v z) := by
    simpa [mul_comm] using hprod'
  rw [hij, hji]
  linarith

theorem integral_timeDeriv_mul_constantPrincipal_eq_zero
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hA : ∀ i j, A i j = A j i) :
    (∫ z, timeDeriv v z * constantPrincipal A v z) = 0 := by
  let I : Fin n → Fin n → ℝ := fun i j =>
    ∫ z, timeDeriv v z * spatialSecond i j v z
  have hterm (i j : Fin n) :
      Integrable (fun z => A i j * (timeDeriv v z * spatialSecond i j v z)) volume := by
    exact (integrable_mul_spatialSecond hv hvc i j).const_mul (A i j) |>.congr
      (Filter.Eventually.of_forall (fun z => by ring))
  have hinner (i : Fin n) :
      (∫ z, ∑ j, A i j * (timeDeriv v z * spatialSecond i j v z)) =
        ∑ j, A i j * I i j := by
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← integral_const_mul]
    · intro j hj
      exact hterm i j
  have hexpand :
      (∫ z, timeDeriv v z * constantPrincipal A v z) =
        ∑ i, ∑ j, A i j * I i j := by
    have hpoint : (fun z => timeDeriv v z * constantPrincipal A v z) =
        (fun z => ∑ i, ∑ j, A i j * (timeDeriv v z * spatialSecond i j v z)) := by
      funext z
      simp only [constantPrincipal]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hpoint, integral_finsetSum Finset.univ]
    · simp_rw [hinner]
    · intro i hi
      apply integrable_finsetSum
      intro j hj
      exact hterm i j
  rw [hexpand]
  have hpair (i j : Fin n) : I i j + I j i = 0 :=
    integral_timeDeriv_mul_spatialSecond_pair_zero hv hvc i j
  have hweighted (i j : Fin n) : A i j * I i j + A j i * I j i = 0 := by
    rw [hA i j]
    rw [← mul_add, hpair, mul_zero]
  have htranspose : (∑ i, ∑ j, A i j * I i j) =
      ∑ i, ∑ j, A j i * I j i := by
    calc
      (∑ i, ∑ j, A i j * I i j) = ∑ j, ∑ i, A i j * I i j := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, A j i * I j i := rfl
  have hdouble : (∑ i, ∑ j, A i j * I i j) +
      (∑ i, ∑ j, A i j * I i j) = 0 := by
    calc
      (∑ i, ∑ j, A i j * I i j) + (∑ i, ∑ j, A i j * I i j) =
          (∑ i, ∑ j, A i j * I i j) + (∑ i, ∑ j, A j i * I j i) := by
        rw [htranspose]
      _ = ∑ i, ∑ j, (A i j * I i j + A j i * I j i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        exact hweighted i j
  linarith

theorem constant_energy_identity_of_cross_zero
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hvt : Integrable (fun z => (timeDeriv v z) ^ 2) volume)
    (hprincipal : Integrable (fun z => (constantPrincipal A v z) ^ 2) volume)
    (hcross : Integrable (fun z => timeDeriv v z * constantPrincipal A v z) volume)
    (hcross_zero : (∫ z, timeDeriv v z * constantPrincipal A v z) = 0) :
    (∫ z, (timeDeriv v z) ^ 2) + (∫ z, (constantPrincipal A v z) ^ 2) =
      ∫ z, (timeDeriv v z - constantPrincipal A v z) ^ 2 := by
  have hsum : Integrable (fun z => (timeDeriv v z) ^ 2 +
      (constantPrincipal A v z) ^ 2) := hvt.add hprincipal
  have hpoint : (fun z => (timeDeriv v z - constantPrincipal A v z) ^ 2) =
      (fun z => (timeDeriv v z) ^ 2 + (constantPrincipal A v z) ^ 2 -
        2 * (timeDeriv v z * constantPrincipal A v z)) := by
    funext z
    ring
  rw [hpoint]
  have hadd := integral_add hvt hprincipal
  have hdecomp := integral_sub hsum (hcross.const_mul 2)
  rw [hdecomp, hadd, integral_const_mul, hcross_zero]
  ring

theorem constant_parabolic_l2_coercivity_of_principal_bound
    {A : Fin n → Fin n → ℝ} {κ : ℝ} {v : Spacetime n → ℝ}
    (hvt : Integrable (fun z => (timeDeriv v z) ^ 2) volume)
    (hprincipal : Integrable (fun z => (constantPrincipal A v z) ^ 2) volume)
    (hcross : Integrable (fun z => timeDeriv v z * constantPrincipal A v z) volume)
    (hcross_zero : (∫ z, timeDeriv v z * constantPrincipal A v z) = 0)
    (hbound : κ ^ 2 * (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      ∫ z, (constantPrincipal A v z) ^ 2) :
    (∫ z, (timeDeriv v z) ^ 2) + κ ^ 2 *
        (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      ∫ z, (timeDeriv v z - constantPrincipal A v z) ^ 2 := by
  have hid := constant_energy_identity_of_cross_zero hvt hprincipal hcross hcross_zero
  calc
    (∫ z, (timeDeriv v z) ^ 2) + κ ^ 2 *
        (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      (∫ z, (timeDeriv v z) ^ 2) + ∫ z, (constantPrincipal A v z) ^ 2 :=
        add_le_add (le_refl _) hbound
    _ = ∫ z, (timeDeriv v z - constantPrincipal A v z) ^ 2 := hid

theorem constant_parabolic_l2_coercivity_smooth_compact_support
    {A : Fin n → Fin n → ℝ} {κ : ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hcross_zero : (∫ z, timeDeriv v z * constantPrincipal A v z) = 0)
    (hbound : κ ^ 2 * (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      ∫ z, (constantPrincipal A v z) ^ 2) :
    (∫ z, (timeDeriv v z) ^ 2) + κ ^ 2 *
        (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      ∫ z, (timeDeriv v z - constantPrincipal A v z) ^ 2 := by
  exact constant_parabolic_l2_coercivity_of_principal_bound
    (integrable_timeDeriv_sq hv hvc)
    (integrable_constantPrincipal_sq hv hvc)
    (integrable_timeDeriv_mul_constantPrincipal hv hvc)
    hcross_zero hbound

theorem constant_parabolic_l2_coercivity
    {A : Fin n → Fin n → ℝ} {κ : ℝ} {v : Spacetime n → ℝ}
    (hA : ∀ i j, A i j = A j i) (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, A i j * ξ i * ξ j)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    (∫ z, (timeDeriv v z) ^ 2) + κ ^ 2 *
        (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      ∫ z, (timeDeriv v z - constantPrincipal A v z) ^ 2 := by
  exact constant_parabolic_l2_coercivity_smooth_compact_support hv hvc
    (integral_timeDeriv_mul_constantPrincipal_eq_zero hv hvc hA)
    (integral_principal_sq_ge hv hvc (le_of_lt hκ) hEll)

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
