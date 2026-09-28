




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Bootstrap











open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

private theorem time_hessian_pairing_zero
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (i j : Fin n) :
    (∫ z, timeDeriv v z * spatialSecond i j v z) = 0 := by
  have h := integral_timeDeriv_mul_spatialSecond_pair_zero hv hvc i j
  have he : spatialSecond j i v = spatialSecond i j v := by
    funext z
    exact spatialSecond_comm v hv j i z
  rw [he] at h
  linarith

private theorem time_principal_pairing_zero
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    (∫ z, timeDeriv v z * constantPrincipal A v z) = 0 := by
  have hterm (i j : Fin n) :
      Integrable (fun z => A i j * (timeDeriv v z * spatialSecond i j v z)) := by
    exact (integrable_mul_spatialSecond hv hvc i j).const_mul (A i j) |>.congr
      (Eventually.of_forall (fun z => by ring))
  have he : (fun z => timeDeriv v z * constantPrincipal A v z) =
      (fun z => ∑ i, ∑ j, A i j * (timeDeriv v z * spatialSecond i j v z)) := by
    funext z
    simp only [constantPrincipal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => hterm i j)]
  simp_rw [integral_const_mul, time_hessian_pairing_zero hv hvc]
  simp

private theorem integrable_variable_principal_sq
    {a : Fin n → Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, Continuous (a i j))
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) :
    Integrable (fun z => (∑ i, ∑ j, a i j z * spatialSecond i j v z) ^ 2) := by
  have hc : Continuous (fun z => ∑ i, ∑ j, a i j z * spatialSecond i j v z) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => (ha i j).mul (contDiff_spatialSecond hv i j).continuous))
  have hs : HasCompactSupport (fun z => ∑ i, ∑ j, a i j z * spatialSecond i j v z) := by
    have hs' : HasCompactSupport (∑ i : Fin n, ∑ j : Fin n,
        a i j * spatialSecond i j v) :=
      HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ =>
        HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ =>
          (hasCompactSupport_spatialSecond i j hvc).mul_left
            (f := a i j)))
    have he : (∑ i : Fin n, ∑ j : Fin n, a i j * spatialSecond i j v) =
        (fun z => ∑ i, ∑ j, a i j z * spatialSecond i j v z) := by
      funext z
      simp
    rw [← he]
    exact hs'
  convert (hc.mul hc).integrable_of_hasCompactSupport
    (μ := (volume : Measure (Spacetime n))) hs.mul_right using 1
  ext z
  simp only [pow_two, Pi.mul_apply]

private theorem hessian_zero_off_support
    {v : Spacetime n → ℝ} {z : Spacetime n} (hz : z ∉ tsupport v)
    (i j : Fin n) : spatialSecond i j v z = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hz
  exact ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans
    (tsupport_fderiv_apply_subset ℝ (spatialDirection j))) h

private theorem principal_error_sq_le
    {A : Fin n → Fin n → ℝ} {a : Fin n → Fin n → Spacetime n → ℝ}
    {v : Spacetime n → ℝ} {ε : ℝ}
    (hosc : ∀ z ∈ tsupport v, (∑ i, ∑ j, (a i j z - A i j) ^ 2) ≤ ε ^ 2)
    (z : Spacetime n) :
    (∑ i, ∑ j, (a i j z - A i j) * spatialSecond i j v z) ^ 2 ≤
      ε ^ 2 * (∑ i, ∑ j, (spatialSecond i j v z) ^ 2) := by
  by_cases hz : z ∈ tsupport v
  · have hCS := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n × Fin n))
      (fun p => a p.1 p.2 z - A p.1 p.2)
      (fun p => spatialSecond p.1 p.2 v z)
    simp only [Fintype.sum_prod_type] at hCS
    exact hCS.trans (mul_le_mul_of_nonneg_right (hosc z hz)
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))))
  · simp only [hessian_zero_off_support hz, mul_zero, Finset.sum_const_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, le_refl]



theorem variable_principal_parabolic_coercivity
    {A : Fin n → Fin n → ℝ} {a : Fin n → Fin n → Spacetime n → ℝ}
    {κ ε : ℝ} (hκ : 0 < κ) (_hsmall : 2 * ε ^ 2 < κ ^ 2)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j)
    (ha : ∀ i j, Continuous (a i j))
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hosc : ∀ z ∈ tsupport v, (∑ i, ∑ j, (a i j z - A i j) ^ 2) ≤ ε ^ 2) :
    (∫ z, (timeDeriv v z) ^ 2) + (κ ^ 2 - 2 * ε ^ 2) *
        (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      2 * (∫ z, (timeDeriv v z - ∑ i, ∑ j, a i j z * spatialSecond i j v z) ^ 2) := by
  let R : Spacetime n → ℝ := fun z =>
    timeDeriv v z - ∑ i, ∑ j, a i j z * spatialSecond i j v z
  let E : Spacetime n → ℝ := fun z =>
    ∑ i, ∑ j, (a i j z - A i j) * spatialSecond i j v z
  let H : Spacetime n → ℝ := fun z => ∑ i, ∑ j, (spatialSecond i j v z) ^ 2
  have hE : Integrable (fun z => E z ^ 2) :=
    integrable_variable_principal_sq (fun i j => (ha i j).sub continuous_const) hv hvc
  have hH : Integrable H := integrable_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun j _ => integrable_spatialSecond_sq hv hvc i j))
  have hP := integrable_variable_principal_sq ha hv hvc
  have hT := integrable_timeDeriv_sq hv hvc
  have hR : Integrable (fun z => R z ^ 2) := by
    apply ((hT.const_mul 2).add (hP.const_mul 2)).mono_nonneg
    · exact (((contDiff_timeDeriv hv).continuous.sub
        (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
          (fun j _ => (ha i j).mul (contDiff_spatialSecond hv i j).continuous)))).pow 2).aestronglyMeasurable
    · exact Eventually.of_forall (fun z => sq_nonneg _)
    · filter_upwards [] with z
      dsimp [R]
      nlinarith [sq_nonneg (timeDeriv v z + ∑ i, ∑ j, a i j z * spatialSecond i j v z)]
  have heq : (fun z => R z + E z) =
      (fun z => timeDeriv v z - constantPrincipal A v z) := by
    funext z
    simp only [R, E, constantPrincipal, sub_mul, Finset.sum_sub_distrib]
    ring
  have hRE : Integrable (fun z => (R z + E z) ^ 2) := by
    simp_rw [congrFun heq]
    have hPA := integrable_constantPrincipal_sq (A := A) hv hvc
    apply ((hT.const_mul 2).add (hPA.const_mul 2)).mono_nonneg
    · exact (((contDiff_timeDeriv hv).sub (contDiff_constantPrincipal hv)).pow 2).continuous.aestronglyMeasurable
    · exact Eventually.of_forall (fun z => sq_nonneg _)
    · filter_upwards [] with z
      dsimp
      nlinarith [sq_nonneg (timeDeriv v z + constantPrincipal A v z)]
  have hbound : (∫ z, E z ^ 2) ≤ ε ^ 2 * (∫ z, H z) := by
    calc
      (∫ z, E z ^ 2) ≤ ∫ z, ε ^ 2 * H z :=
        integral_mono_ae hE (hH.const_mul _) (Eventually.of_forall (principal_error_sq_le hosc))
      _ = ε ^ 2 * (∫ z, H z) := integral_const_mul _ _
  have hsplit := integral_sq_add_le hR hE hRE
  simp_rw [congrFun heq] at hsplit
  have hfrozen := constant_parabolic_l2_coercivity_smooth_compact_support hv hvc
    (time_principal_pairing_zero hv hvc) (integral_principal_sq_ge hv hvc hκ.le hEll)
  change (∫ z, (timeDeriv v z) ^ 2) + (κ ^ 2 - 2 * ε ^ 2) * (∫ z, H z) ≤
    2 * (∫ z, R z ^ 2)
  change (∫ z, (timeDeriv v z) ^ 2) + κ ^ 2 * (∫ z, H z) ≤ _ at hfrozen
  linarith

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
