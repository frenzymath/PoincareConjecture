




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.ForcedSecondJets









open Set MeasureTheory Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

private theorem adjoint_zero_off_test {n : ℕ} (C : Coefficients n)
    (φ : Spacetime n → ℝ) {y : Spacetime n} (hy : y ∉ tsupport φ) :
    C.adjoint φ y = 0 := by
  have hD {a : Spacetime n → ℝ} (ha : tsupport a ⊆ tsupport φ) (v : Spacetime n) :
      fderiv ℝ a y v = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ a x v)
      (fun h => hy (((tsupport_fderiv_apply_subset ℝ v).trans ha) h))
  have ht : timeDeriv φ y = 0 := hD Subset.rfl (0, 1)
  have hss (i j : Fin n) :
      spatialDeriv j (spatialDeriv i (fun x => C.principal i j x * φ x)) y = 0 :=
    hD ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans
      tsupport_mul_subset_right) (spatialDirection j)
  have hd (i : Fin n) : spatialDeriv i (fun x => C.drift i x * φ x) y = 0 :=
    hD tsupport_mul_subset_right (spatialDirection i)
  simp only [Coefficients.adjoint, ht, hss, hd, image_eq_zero_of_notMem_tsupport hy,
    Finset.sum_const_zero, neg_zero, sub_zero, mul_zero, add_zero]

theorem exists_local_forced_weak_second_jets_of_memLpOn
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn Set.univ)
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzerothc : HasCompactSupport C.zeroth)
    {u f : Spacetime n → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict U))
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y)
    (hweak : ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ y in U, φ y * g i y) = -(∫ y in U, spatialDeriv i φ y * u y))
    {z : Spacetime n} (hz : z ∈ U) {κ : ℝ} (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, C.principal i j z * ξ i * ξ j) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      ∃ (T : Spacetime n → ℝ) (H : Fin n → Fin n → Spacetime n → ℝ),
        MemLp T 2 volume ∧ (∀ i j, MemLp (H i j) 2 volume) ∧
        (∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * g i y) =
            -(∫ y in ball z r, spatialDeriv i φ y * u y)) ∧
        (∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * T y) =
            -(∫ y in ball z r, timeDeriv φ y * u y)) ∧
        (∀ i j (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * H i j y) =
            -(∫ y in ball z r, spatialDeriv i φ y * g j y)) := by
  classical
  let u' := U.indicator u
  let f' := U.indicator f
  let g' (i : Fin n) := U.indicator (g i)
  have hu' : MemLp u' 2 volume := (memLp_indicator_iff_restrict hU.measurableSet).mpr hu
  have hf' : MemLp f' 2 volume := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf
  have hg' (i : Fin n) : MemLp (g' i) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).mpr (hg i)
  have hpair {A : Set (Spacetime n)} (hA : MeasurableSet A) (hAU : A ⊆ U)
      (ψ v : Spacetime n → ℝ) :
      (∫ y in A, ψ y * U.indicator v y) = ∫ y in A, ψ y * v y := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [indicator_of_mem (hAU hy)]
  have hforce' (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ U) :
      (∫ y, u' y * C.adjoint φ y) = ∫ y, φ y * f' y := by
    calc
      (∫ y, u' y * C.adjoint φ y) = ∫ y, u y * C.adjoint φ y := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ U
        · rw [show u' y = u y from indicator_of_mem hy _]
        · rw [adjoint_zero_off_test C φ (fun h => hy (hφs h)), mul_zero, mul_zero]
      _ = ∫ y, φ y * f y := hforce φ hφ hφc hφs
      _ = ∫ y, φ y * f' y := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ U
        · rw [show f' y = f y from indicator_of_mem hy _]
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφs h)), zero_mul, zero_mul]
  have hweak' (i : Fin n) (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ U) :
      (∫ y in U, φ y * g' i y) = -(∫ y in U, spatialDeriv i φ y * u' y) := by
    change (∫ y in U, φ y * U.indicator (g i) y) =
      -(∫ y in U, spatialDeriv i φ y * U.indicator u y)
    rw [hpair hU.measurableSet Subset.rfl, hpair hU.measurableSet Subset.rfl]
    exact hweak i φ hφ hφc hφs
  obtain ⟨r, hr, hrU, T, H, hT, hH, hgw, hTw, hHw⟩ :=
    exists_local_forced_weak_second_jets hU hC hprincipalc hdriftc hzerothc
      hu' hf' hg' hforce' hweak' hz hκ hEll
  have hballU : ball z r ⊆ U := ball_subset_closedBall.trans hrU
  refine ⟨r, hr, hrU, T, H, hT, hH, ?_, ?_, ?_⟩
  · intro i φ hφ hφc hφs
    have he := hgw i φ hφ hφc hφs
    change (∫ y in ball z r, φ y * U.indicator (g i) y) =
      -(∫ y in ball z r, spatialDeriv i φ y * U.indicator u y) at he
    rwa [hpair measurableSet_ball hballU, hpair measurableSet_ball hballU] at he
  · intro φ hφ hφc hφs
    have he := hTw φ hφ hφc hφs
    change (∫ y in ball z r, φ y * T y) =
      -(∫ y in ball z r, timeDeriv φ y * U.indicator u y) at he
    rwa [hpair measurableSet_ball hballU] at he
  · intro i j φ hφ hφc hφs
    have he := hHw i j φ hφ hφc hφs
    change (∫ y in ball z r, φ y * H i j y) =
      -(∫ y in ball z r, spatialDeriv i φ y * U.indicator (g j) y) at he
    rwa [hpair measurableSet_ball hballU] at he


end Poincare.Analysis.Parabolic.WeakRegularity.Interior
