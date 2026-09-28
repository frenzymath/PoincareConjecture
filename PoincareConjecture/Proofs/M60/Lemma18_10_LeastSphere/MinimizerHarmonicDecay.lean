import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Uniform
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerPlanePoisson
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakRescaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "L" => secondOrderOperator (fun _ : Plane => (1 : Matrix (Fin 2) (Fin 2) ℝ))
  (fun _ : Fin 2 => fun _ : Plane => (0 : ℝ))

theorem suPlaneLaplace_rescale (u : Plane → ℝ) (a : Plane) (s : ℝ) (z : Plane) :
    L (fun y => u (a + s • y)) z = s ^ 2 * L u (a + s • z) := by
  have hform (f : Plane → ℝ) (x : Plane) : L f x =
      partialDeriv 0 (partialDeriv 0 f) x + partialDeriv 1 (partialDeriv 1 f) x := by
    simp [secondOrderOperator, Matrix.one_apply, Fin.sum_univ_two]
  have hscale (i : Fin 2) :
      partialDeriv i (partialDeriv i (fun y => u (a + s • y))) z =
        s ^ 2 * partialDeriv i (partialDeriv i u) (a + s • z) :=
    suRescale_second_fderiv u a s z (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
  rw [hform, hform]
  rw [hscale, hscale]
  ring

theorem suPlaneLaplace_partial {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 2) :
    L (partialDeriv i u) = partialDeriv i (L u) := by
  have hform (f : Plane → ℝ) : L f = fun x =>
      partialDeriv 0 (partialDeriv 0 f) x + partialDeriv 1 (partialDeriv 1 f) x := by
    ext x
    simp [secondOrderOperator, Matrix.one_apply, Fin.sum_univ_two]
  rw [hform, hform]
  rw [partial_comm hu 0 i, partial_comm hu 1 i,
    partial_comm (contDiff_partial hu 0) 0 i,
    partial_comm (contDiff_partial hu 1) 1 i]
  funext x
  exact congrArg (fun A : Plane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) (fderiv_fun_add
    ((contDiff_partial (contDiff_partial hu 0) 0).differentiable (by simp) x)
    ((contDiff_partial (contDiff_partial hu 1) 1).differentiable (by simp) x)).symm

theorem suHarmonic_unit_value_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Plane → ℝ},
      ContDiffOn ℝ ∞ u (Metric.ball 0 1) →
      EqOn (L u) (fun _ => 0) (Metric.ball 0 1) →
      MemLp u 2 (volume.restrict (Metric.ball 0 1)) →
      ∀ x ∈ Metric.closedBall 0 (1 / 2),
        u x ^ 2 ≤ C * ∫ y in Metric.ball 0 1, u y ^ 2 := by
  let O : Set Plane := Metric.ball 0 1
  let V : Set Plane := Metric.ball 0 (3 / 4)
  let K : Set Plane := Metric.closedBall 0 (1 / 2)
  have hVc : IsCompact (closure V) := by
    simpa only [V, closure_ball (0 : Plane) (by norm_num : (3 / 4 : ℝ) ≠ 0)] using
      isCompact_closedBall (0 : Plane) (3 / 4 : ℝ)
  have hVO : closure V ⊆ O :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num))
  have hKV : K ⊆ V := Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨q, C, hC, hbound⟩ := uniform_interior_estimate_of_elliptic_powers
    Metric.isOpen_ball Metric.isOpen_ball hVc hVO (isCompact_closedBall _ _) hKV
    (fun _ : Plane => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (fun _ : Fin 2 => fun _ : Plane => (0 : ℝ))
    (fun _ _ => contDiffOn_const) (fun _ _ => Matrix.PosDef.one)
    (fun _ => contDiffOn_const) 0
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro u hu hzero hm x hx
  have hiter (j : ℕ) : EqOn (L^[j + 1] u) (fun _ => 0) O := by
    induction j with
    | zero => simpa using hzero
    | succ j ih =>
      have h := secondOrderOperator_eqOn (b := fun _ : Fin 2 => fun _ : Plane => (0 : ℝ))
        Metric.isOpen_ball
        (show EqOn (fun _ : Plane => (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (fun _ : Plane => (1 : Matrix (Fin 2) (Fin 2) ℝ)) O from fun _ _ => rfl)
        (fun _ _ _ => rfl) ih
      have hz : L (fun _ => 0) = fun _ => 0 := by
        have hp (i : Fin 2) : partialDeriv i (fun _ : Plane => (0 : ℝ)) = fun _ => 0 := by
          ext z
          simp [partialDeriv]
        ext y
        simp only [secondOrderOperator, hp, mul_zero, Finset.sum_const_zero, zero_add]
      rw [hz] at h
      simpa only [Function.iterate_succ_apply'] using h
  have hsum : (∑ j ∈ Finset.range (q + 1),
      (eLpNorm (L^[j] u) 2 (volume.restrict V)).toReal) =
      (eLpNorm u 2 (volume.restrict V)).toReal := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have heq : (L^[k + 1] u) =ᵐ[volume.restrict V] fun _ => 0 := by
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
        exact hiter k (hVO (subset_closure hy))
      rw [eLpNorm_congr_ae heq]
      simp
    · simp
  have hb := hbound hu x hx
  rw [norm_iteratedFDeriv_zero, hsum] at hb
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le ENNReal.toReal_nonneg)).mpr hb
  have hmV := hm.mono_measure (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
  rw [mul_pow, eLpNorm_toReal_sq_eq_integral hmV, Real.norm_eq_abs, sq_abs] at hs
  refine hs.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg C))
  exact integral_mono_measure (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
    (Eventually.of_forall fun y => sq_nonneg _) hm.integrable_sq

theorem suHarmonic_disk_value_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Plane → ℝ} (a : Plane) {R : ℝ}, 0 < R →
      ContDiffOn ℝ ∞ u (Metric.ball a R) →
      EqOn (L u) (fun _ => 0) (Metric.ball a R) →
      MemLp u 2 (volume.restrict (Metric.ball a R)) →
      ∀ x ∈ Metric.closedBall a (R / 2),
        R ^ 2 * u x ^ 2 ≤ C * ∫ y in Metric.ball a R, u y ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := suHarmonic_unit_value_bound
  refine ⟨C, hC, ?_⟩
  intro u a R hR hu hzero hm x hx
  let A : Plane → Plane := fun y => a + R • y
  have hmap : MapsTo A (Metric.ball 0 1) (Metric.ball a R) := by
    intro y hy
    have h := mem_image_of_mem A hy
    rwa [suAffine_image_ball a hR, mul_one] at h
  have hpre : A ⁻¹' Metric.ball a R = Metric.ball 0 1 := by
    simpa only [mul_one] using suAffine_preimage_ball a hR 1
  have hv : ContDiffOn ℝ ∞ (u ∘ A) (Metric.ball 0 1) :=
    hu.comp (contDiff_const.add (contDiff_id.const_smul R)).contDiffOn hmap
  have hz : EqOn (L (u ∘ A)) (fun _ => 0) (Metric.ball 0 1) := by
    intro y hy
    change L (fun w => u (a + R • w)) y = 0
    rw [suPlaneLaplace_rescale, hzero (hmap hy), mul_zero]
  have hvm : MemLp (u ∘ A) 2 (volume.restrict (Metric.ball 0 1)) := by
    have h := suAffine_memLp hm a hR
    change MemLp (u ∘ A) 2 (volume.restrict (A ⁻¹' Metric.ball a R)) at h
    rwa [hpre] at h
  have him : A '' Metric.closedBall 0 (1 / 2) = Metric.closedBall a (R / 2) := by
    simpa only [mul_one_div] using suRescale_closedBall a hR (1 / 2)
  have hximage : x ∈ A '' Metric.closedBall 0 (1 / 2) := by rwa [him]
  obtain ⟨y, hy, hxy⟩ := hximage
  have hb := hbound hv hz hvm y hy
  have hi : R ^ 2 * (∫ y in Metric.ball 0 1, (u ∘ A) y ^ 2) =
      ∫ y in Metric.ball a R, u y ^ 2 := by
    rw [← integral_const_mul]
    simpa only [suAffine_image_ball a hR, mul_one, A, Function.comp_apply] using
      suRescale_integral (fun y => u y ^ 2) a hR (Metric.ball 0 1)
  have hs := mul_le_mul_of_nonneg_left hb (sq_nonneg R)
  change R ^ 2 * u (A y) ^ 2 ≤ R ^ 2 * (C * ∫ z in Metric.ball 0 1, (u ∘ A) z ^ 2) at hs
  rw [hxy, ← mul_assoc, mul_comm (R ^ 2) C, mul_assoc, hi] at hs
  exact hs

theorem suHarmonic_disk_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Plane → ℝ} (a : Plane) {R r : ℝ},
      0 < R → 0 < r → r ≤ R / 2 →
      ContDiffOn ℝ ∞ u (Metric.ball a R) →
      EqOn (L u) (fun _ => 0) (Metric.ball a R) →
      MemLp u 2 (volume.restrict (Metric.ball a R)) →
      (∫ y in Metric.ball a r, u y ^ 2) ≤
        C * (r / R) ^ 2 * ∫ y in Metric.ball a R, u y ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := suHarmonic_disk_value_bound
  refine ⟨Real.pi * C, mul_pos Real.pi_pos hC, ?_⟩
  intro u a R r hR hr hrR hu hz hm
  let energy := ∫ y in Metric.ball a R, u y ^ 2
  have hpoint (x : Plane) (hx : x ∈ Metric.ball a r) :
      u x ^ 2 ≤ C * energy / R ^ 2 := by
    have hx' : x ∈ Metric.closedBall a (R / 2) :=
      Metric.closedBall_subset_closedBall hrR (Metric.ball_subset_closedBall hx)
    exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr
      (by simpa only [mul_comm (R ^ 2)] using hbound a hR hu hz hm x hx')
  have hsub : Metric.ball a r ⊆ Metric.ball a R :=
    Metric.ball_subset_ball (hrR.trans (by linarith))
  have hi := (hm.mono_measure (Measure.restrict_mono hsub le_rfl)).integrable_sq
  have hle := setIntegral_mono_on hi
    (integrableOn_const (μ := (volume : Measure Plane)) (measure_ball_lt_top.ne))
    Metric.isOpen_ball.measurableSet hpoint
  have hvol : volume.real (Metric.ball a r) = r ^ 2 * Real.pi := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [setIntegral_const, hvol, smul_eq_mul] at hle
  exact hle.trans_eq (by dsimp only [energy]; rw [div_pow]; ring)

end PoincareConjecture.M60

end
