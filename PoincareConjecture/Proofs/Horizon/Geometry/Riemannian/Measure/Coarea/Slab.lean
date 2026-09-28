import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Weighted
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Interval
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakDerivative.Interval
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

theorem integral_slab_eq_level_sub_of_cutoff
    {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (hKU : f ⁻¹' Icc a b ⊆ U)
    {A H : M → ℝ} (hA : ContinuousOn A U) (hH : ContinuousOn H U)
    (hcutoff : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b →
      (∫ x, η (f x) * A x ∂g.volumeMeasure) =
        ∫ x, -deriv η (f x) * H x * g.tangentNorm x (g.gradient f x)
          ∂g.volumeMeasure) :
    (∫ x in f ⁻¹' Icc a b, A x ∂g.volumeMeasure) =
      (∫ z, H (openLevelIncl f U b z) ∂g.regularLevelVolume hf U hreg b) -
        ∫ z, H (openLevelIncl f U a z) ∂g.regularLevelVolume hf U hreg a := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  obtain ⟨χ, hχone, hχcompact, hχsupport, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hcompact U.isOpen hKU
  let s : M → ℝ := fun x => g.tangentNorm x (g.gradient f x)
  have hscont : Continuous s := g.continuous_tangentNorm_gradient hf
  have hsne (x : M) (hx : x ∈ U) : s x ≠ 0 :=
    ((g.tangentNorm_gradient_pos_iff f x).mpr (hreg x hx)).ne'
  let P : M → ℝ := fun x => χ x * (A x / s x)
  let Q : M → ℝ := fun x => χ x * H x
  have hPs : tsupport P ⊆ U := tsupport_mul_subset_left.trans hχsupport
  have hQs : tsupport Q ⊆ U := tsupport_mul_subset_left.trans hχsupport
  have hPc : HasCompactSupport P := (show HasCompactSupport (χ : M → ℝ) from hχcompact).mul_right
  have hQc : HasCompactSupport Q := (show HasCompactSupport (χ : M → ℝ) from hχcompact).mul_right
  have hP : Continuous P :=
    (χ.continuous.continuousOn.mul (hA.div hscont.continuousOn hsne)).continuous_of_tsupport_subset
      U.isOpen hPs
  have hQ : Continuous Q :=
    (χ.continuous.continuousOn.mul hH).continuous_of_tsupport_subset U.isOpen hQs
  have hPA (x : M) (hx : x ∈ f ⁻¹' Icc a b) : P x * s x = A x := by
    dsimp only [P]
    rw [hχone hx, Pi.one_apply, one_mul, div_mul_cancel₀ _ (hsne x (hKU hx))]
  have hQH (x : M) (hx : x ∈ f ⁻¹' Icc a b) : Q x = H x := by
    dsimp only [Q]
    rw [hχone hx, Pi.one_apply, one_mul]
  let p : ℝ → ℝ := fun c => ∫ z, P (openLevelIncl f U c z)
    ∂g.regularLevelVolume hf U hreg c
  let q : ℝ → ℝ := fun c => ∫ z, Q (openLevelIncl f U c z)
    ∂g.regularLevelVolume hf U hreg c
  have hp : Continuous p := g.continuous_regularLevelIntegral hf U hreg hP hPc hPs
  have hq : Continuous q := g.continuous_regularLevelIntegral hf U hreg hQ hQc hQs
  have hweak (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Ioo a b) :
      (∫ c, η c * p c) = -(∫ c, deriv η c * q c) := by
    calc
      (∫ c, η c * p c) =
          ∫ x, η (f x) * P x * s x ∂g.volumeMeasure :=
        (g.integral_mul_comp_coarea hf U hreg hP hPc hPs hη.continuous).symm
      _ = ∫ x, η (f x) * A x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ f ⁻¹' Icc a b
        · rw [mul_assoc, hPA x hx]
        · have hηzero : η (f x) = 0 := image_eq_zero_of_notMem_tsupport
            (fun ht => hx (Ioo_subset_Icc_self (hηs ht)))
          rw [hηzero, zero_mul, zero_mul, zero_mul]
      _ = ∫ x, -deriv η (f x) * H x * s x ∂g.volumeMeasure := hcutoff η hη hηc hηs
      _ = ∫ x, -deriv η (f x) * Q x * s x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ f ⁻¹' Icc a b
        · rw [hQH x hx]
        · have hdηzero : deriv η (f x) = 0 := image_eq_zero_of_notMem_tsupport
            (fun ht => hx (Ioo_subset_Icc_self (hηs (tsupport_deriv_subset ht))))
          rw [hdηzero, neg_zero, zero_mul, zero_mul, zero_mul, zero_mul]
      _ = ∫ c, -deriv η c * q c :=
        g.integral_mul_comp_coarea hf U hreg hQ hQc hQs
          (hη.continuous_deriv (by simp)).neg
      _ = -(∫ c, deriv η c * q c) := by simp only [neg_mul, integral_neg]
  have hFTC := Poincare.Analysis.WeakDerivative.intervalIntegral_eq_sub_of_weakDerivative_Icc
    hab hp.continuousOn hq.continuousOn hweak
  have hend (c : ℝ) (hc : c ∈ Icc a b) : q c =
      ∫ z, H (openLevelIncl f U c z) ∂g.regularLevelVolume hf U hreg c := by
    apply integral_congr_ae
    filter_upwards [] with z
    apply hQH
    change f (openLevelIncl f U c z) ∈ Icc a b
    rw [show f (openLevelIncl f U c z) = c from z.2]
    exact hc
  calc
    (∫ x in f ⁻¹' Icc a b, A x ∂g.volumeMeasure) =
        ∫ x in f ⁻¹' Icc a b, P x * s x ∂g.volumeMeasure := by
      apply setIntegral_congr_fun (isClosed_Icc.preimage hf.continuous).measurableSet
      intro x hx
      exact (hPA x hx).symm
    _ = ∫ c in Icc a b, p c := g.integral_coarea_Icc hf U hreg hP hPc hPs a b
    _ = ∫ c in a..b, p c := by
      rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]
    _ = q b - q a := hFTC
    _ = _ := by rw [hend b (right_mem_Icc.2 hab.le), hend a (left_mem_Icc.2 hab.le)]

end PoincareConjecture.RiemannianMetric
