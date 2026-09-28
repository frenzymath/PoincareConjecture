import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyMeasurable
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchMeasurableGauge
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

theorem integral_norm_inv_closedBall_le_center {R : ℝ} (hR : 0 < R)
    (c z : ℂ) :
    (∫ u in closedBall c R, ‖z - u‖⁻¹) ≤ 8 * Real.pi * R := by
  have heq : (∫ u in closedBall c R, ‖z - u‖⁻¹) =
      ∫ v in closedBall (0 : ℂ) R, ‖(c - z) - v‖⁻¹ := by
    calc
      _ = ∫ u : ℂ, (closedBall (0 : ℂ) R).indicator
          (fun v => ‖(c - z) - v‖⁻¹) (c - u) := by
        rw [← integral_indicator measurableSet_closedBall]
        apply integral_congr_ae
        filter_upwards with u
        have hm : c - u ∈ closedBall (0 : ℂ) R ↔ u ∈ closedBall c R := by
          simp [dist_eq_norm, norm_sub_rev]
        have hv : (c - z) - (c - u) = u - z := by ring
        by_cases hu : u ∈ closedBall c R <;>
          simp only [indicator, hm, hu, hv, norm_sub_rev, ↓reduceIte]
      _ = _ := by
        rw [integral_sub_left_eq_self, integral_indicator measurableSet_closedBall]
  rw [heq]
  exact integral_norm_inv_closedBall_le_global hR (c - z)

theorem integral_cauchyKernel_sub_le {R : ℝ} (hR : 0 < R) (z w : ℂ) :
    (∫ u in closedBall (0 : ℂ) R, ‖(z - u)⁻¹ - (w - u)⁻¹‖) ≤
      Real.pi * (10 + 8 * R) * Real.sqrt ‖z - w‖ := by
  by_cases hzw : z = w
  · subst w
    simp
  let S := closedBall (0 : ℂ) R
  let d := ‖z - w‖
  let rho := Real.sqrt d
  let A := ball z rho
  let f := fun u : ℂ => ‖(z - u)⁻¹ - (w - u)⁻¹‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hr : 0 < rho := Real.sqrt_pos.mpr hd
  have hi (a c : ℂ) (r : ℝ) :
      IntegrableOn (fun u => ‖a - u‖⁻¹) (closedBall c r) := by
    simpa only [norm_inv, IntegrableOn] using
      ((locallyIntegrable_cauchyKernel_sub a).integrableOn_isCompact
        (isCompact_closedBall c r)).norm
  have hf : IntegrableOn f S :=
    (((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) R)).sub
      ((locallyIntegrable_cauchyKernel_sub w).integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R))).norm
  have hzi : IntegrableOn (fun u => ‖z - u‖⁻¹) (S ∩ A) :=
    (hi z 0 R).mono_set inter_subset_left
  have hwi : IntegrableOn (fun u => ‖w - u‖⁻¹) (S ∩ A) :=
    (hi w 0 R).mono_set inter_subset_left
  have hnearZ : (∫ u in S ∩ A, ‖z - u‖⁻¹) ≤ 2 * Real.pi * rho := by
    calc
      _ ≤ ∫ u in A, ‖z - u‖⁻¹ :=
        setIntegral_mono_set ((hi z z rho).mono_set ball_subset_closedBall)
          (ae_of_all _ fun _ => inv_nonneg.mpr (norm_nonneg _))
          (ae_of_all _ fun _ h => h.2)
      _ = _ := integral_norm_inv_ball_center z hr.le
  have hnearW : (∫ u in S ∩ A, ‖w - u‖⁻¹) ≤ 8 * Real.pi * rho := by
    calc
      _ ≤ ∫ u in closedBall z rho, ‖w - u‖⁻¹ :=
        setIntegral_mono_set (hi w z rho)
          (ae_of_all _ fun _ => inv_nonneg.mpr (norm_nonneg _))
          (ae_of_all _ fun _ h => ball_subset_closedBall h.2)
      _ ≤ _ := integral_norm_inv_closedBall_le_center hr z w
  have hnear : (∫ u in S ∩ A, f u) ≤ 10 * Real.pi * rho := by
    calc
      _ ≤ ∫ u in S ∩ A, ‖z - u‖⁻¹ + ‖w - u‖⁻¹ := by
        apply integral_mono_ae (hf.mono_set inter_subset_left) (hzi.add hwi)
        filter_upwards with u
        simpa only [f, norm_inv, Pi.add_apply] using norm_sub_le ((z - u)⁻¹) ((w - u)⁻¹)
      _ = (∫ u in S ∩ A, ‖z - u‖⁻¹) + ∫ u in S ∩ A, ‖w - u‖⁻¹ :=
        integral_add hzi hwi
      _ ≤ _ := by linarith only [hnearZ, hnearW]
  have hfarW : (∫ u in S \ A, ‖w - u‖⁻¹) ≤ 8 * Real.pi * R := by
    calc
      _ ≤ ∫ u in S, ‖w - u‖⁻¹ :=
        setIntegral_mono_set (hi w 0 R)
          (ae_of_all _ fun _ => inv_nonneg.mpr (norm_nonneg _))
          (ae_of_all _ fun _ h => h.1)
      _ ≤ _ := integral_norm_inv_closedBall_le_global hR w
  have hfar : (∫ u in S \ A, f u) ≤ (d / rho) * (8 * Real.pi * R) := by
    calc
      _ ≤ ∫ u in S \ A, (d / rho) * ‖w - u‖⁻¹ := by
        apply integral_mono_ae (hf.mono_set sdiff_subset)
          (((hi w 0 R).mono_set sdiff_subset).const_mul (d / rho))
        filter_upwards [ae_restrict_mem (measurableSet_closedBall.diff measurableSet_ball),
          ae_restrict_of_ae (volume.ae_ne z), ae_restrict_of_ae (volume.ae_ne w)]
          with u hu huz huw
        have hzu : z - u ≠ 0 := sub_ne_zero.mpr huz.symm
        have hwu : w - u ≠ 0 := sub_ne_zero.mpr huw.symm
        have hlower : rho ≤ ‖z - u‖ := by
          simpa only [A, mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hu.2
        have hinv : (z - u)⁻¹ - (w - u)⁻¹ = (w - z) / ((z - u) * (w - u)) := by
          field_simp [hzu, hwu]
          ring
        calc
          f u = (d / ‖z - u‖) * ‖w - u‖⁻¹ := by
            dsimp only [f]
            rw [hinv, norm_div, norm_mul, norm_sub_rev]
            simp only [d, div_eq_mul_inv, mul_inv_rev]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left hd.le hr hlower) (inv_nonneg.mpr (norm_nonneg _))
      _ = (d / rho) * ∫ u in S \ A, ‖w - u‖⁻¹ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hfarW (div_nonneg hd.le hr.le)
  have hdr : d / rho = rho := by
    apply (div_eq_iff hr.ne').mpr
    simpa only [rho, ← sq] using (Real.sq_sqrt hd.le).symm
  have hsplit := integral_inter_add_sdiff (μ := volume) (s := S) (t := A)
    measurableSet_ball hf
  change (∫ u in S, f u) ≤ _
  rw [← hsplit]
  rw [hdr] at hfar
  nlinarith only [hnear, hfar]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_cauchyOperator_sub_le_sqrt {h : ℂ → E} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : AEStronglyMeasurable h volume)
    (hsupport : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hbound : ∀ u, ‖h u‖ ≤ B) (z w : ℂ) :
    ‖cauchyOperator h z - cauchyOperator h w‖ ≤
      B * (10 + 8 * R) * Real.sqrt ‖z - w‖ := by
  have hiz := integrable_cauchyOperator_of_bound hh hsupport hbound z
  have hiw := integrable_cauchyOperator_of_bound hh hsupport hbound w
  have hid : Integrable (fun u : ℂ => ((z - u)⁻¹ - (w - u)⁻¹) • h u) := by
    simpa only [sub_smul, Pi.sub_def] using hiz.sub hiw
  have heq : cauchyOperator h z - cauchyOperator h w =
      (Real.pi : ℂ)⁻¹ • ∫ u in closedBall (0 : ℂ) R,
        ((z - u)⁻¹ - (w - u)⁻¹) • h u := by
    rw [cauchyOperator, cauchyOperator, ← smul_sub, ← integral_sub hiz hiw]
    simp_rw [← sub_smul]
    congr 1
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [Function.notMem_support.mp (fun h => hu (hsupport h)), smul_zero])).symm
  have hk : IntegrableOn (fun u : ℂ => ‖(z - u)⁻¹ - (w - u)⁻¹‖)
      (closedBall (0 : ℂ) R) :=
    (((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) R)).sub
      ((locallyIntegrable_cauchyKernel_sub w).integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R))).norm
  have hint : ‖∫ u in closedBall (0 : ℂ) R, ((z - u)⁻¹ - (w - u)⁻¹) • h u‖ ≤
      (Real.pi * (10 + 8 * R) * Real.sqrt ‖z - w‖) * B := by
    calc
      _ ≤ ∫ u in closedBall (0 : ℂ) R, ‖((z - u)⁻¹ - (w - u)⁻¹) • h u‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in closedBall (0 : ℂ) R, ‖(z - u)⁻¹ - (w - u)⁻¹‖ * B := by
        apply integral_mono_ae hid.integrableOn.norm (hk.mul_const B)
        filter_upwards with u
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hbound u) (norm_nonneg _)
      _ = (∫ u in closedBall (0 : ℂ) R, ‖(z - u)⁻¹ - (w - u)⁻¹‖) * B :=
        integral_mul_const B _
      _ ≤ _ := mul_le_mul_of_nonneg_right (integral_cauchyKernel_sub_le hR z w) hB
  rw [heq, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * ((Real.pi * (10 + 8 * R) * Real.sqrt ‖z - w‖) * B) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by field_simp

theorem norm_cauchyGauge_sub_le_sqrt {B : Type*} [NormedRing B]
    [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]
    {A : ℂ → B} {R B0 : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2) (z w : ℂ) :
    ‖cauchyGauge A z - cauchyGauge A w‖ ≤
      (2 * B0) * (10 + 8 * R) * Real.sqrt ‖z - w‖ := by
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hPb (u : ℂ) : ‖cauchyGauge A u‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add (cauchyGauge A u) (1 : B)
    rw [norm_one] at hh
    linarith [hP.2.2.1 u]
  have hG : AEStronglyMeasurable (fun u => A u * cauchyGauge A u) volume :=
    hA.mul hP.1.aestronglyMeasurable
  have hGs : Function.support (fun u => A u * cauchyGauge A u) ⊆
      closedBall (0 : ℂ) R := (Function.support_mul_subset_left _ _).trans hs
  have hGb (u : ℂ) : ‖A u * cauchyGauge A u‖ ≤ 2 * B0 := by
    calc
      _ ≤ ‖A u‖ * ‖cauchyGauge A u‖ := norm_mul_le _ _
      _ ≤ B0 * 2 := mul_le_mul (hb u) (hPb u) (norm_nonneg _) hB
      _ = _ := mul_comm _ _
  rw [hP.2.1 z, hP.2.1 w, add_sub_add_left_eq_sub]
  exact norm_cauchyOperator_sub_le_sqrt hR (by positivity) hG hGs hGb z w

theorem cauchyGauge_unframed_halfDisk_holder {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B) (hsmall : 8 * R * B < 1 / 2)
    {u : ℂ → Fin n → ℂ}
    {L : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {r : ℝ}
    (hr : 0 < r)
    (hu : ContDiffOn ℝ 1 u (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hL : ContDiffOn ℝ 1 L (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, IsUnit (L z)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im},
      ∀ w ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im},
        ‖Ring.inverse (L z) (cauchyGauge A z (u z)) -
          Ring.inverse (L w) (cauchyGauge A w (u w))‖ ≤ C * Real.sqrt ‖z - w‖ := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let P := cauchyGauge A
  let V := fun z => Ring.inverse (L z)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hKconv : Convex ℝ K := (convex_closedBall (0 : ℂ) r).inter
    ((convex_Ici (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hV : ContDiffOn ℝ 1 V K := by
    intro z hz
    obtain ⟨a, ha⟩ := hunit z hz
    have hi : ContDiffAt ℝ 1 Ring.inverse (L z) := by
      simpa only [ha] using contDiffAt_ringInverse ℝ (n := 1) a
    exact hi.comp_contDiffWithinAt z (hL z hz)
  obtain ⟨kV, hkV⟩ := hV.exists_lipschitzOnWith one_ne_zero hKconv hK
  obtain ⟨ku, hku⟩ := hu.exists_lipschitzOnWith one_ne_zero hKconv hK
  obtain ⟨Cv0, hCv0⟩ := hK.exists_bound_of_continuousOn hV.continuousOn
  obtain ⟨Cu0, hCu0⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  let Cv := max Cv0 0
  let Cu := max Cu0 0
  have hCv : 0 ≤ Cv := le_max_right _ _
  have hCu : 0 ≤ Cu := le_max_right _ _
  have hvb (z : ℂ) (hz : z ∈ K) : ‖V z‖ ≤ Cv :=
    (hCv0 z hz).trans (le_max_left _ _)
  have hub (z : ℂ) (hz : z ∈ K) : ‖u z‖ ≤ Cu :=
    (hCu0 z hz).trans (le_max_left _ _)
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hPb (z : ℂ) : ‖P z‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add (P z) (1 : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    rw [norm_one] at hh
    linarith [hP.2.2.1 z]
  let Cg := (2 * B) * (10 + 8 * R)
  have hCg : 0 ≤ Cg := by dsimp only [Cg]; positivity
  let C := ((kV : ℝ) * 2 * Cu + Cv * 2 * ku) * Real.sqrt (2 * r) + Cv * Cg * Cu
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro z hz w hw
  have hd : ‖z - w‖ ≤ 2 * r := by
    have hh := norm_sub_le z w
    have hz0 := mem_closedBall_zero_iff.mp hz.1
    have hw0 := mem_closedBall_zero_iff.mp hw.1
    linarith
  have hds : ‖z - w‖ ≤ Real.sqrt (2 * r) * Real.sqrt ‖z - w‖ := by
    calc
      _ = Real.sqrt ‖z - w‖ * Real.sqrt ‖z - w‖ :=
        (Real.mul_self_sqrt (norm_nonneg _)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hd) (Real.sqrt_nonneg _)
  have hVd : ‖V z - V w‖ ≤ (kV : ℝ) * ‖z - w‖ := by
    simpa only [dist_eq_norm] using hkV.dist_le_mul z hz w hw
  have hud : ‖u z - u w‖ ≤ (ku : ℝ) * ‖z - w‖ := by
    simpa only [dist_eq_norm] using hku.dist_le_mul z hz w hw
  have hPd : ‖P z - P w‖ ≤ Cg * Real.sqrt ‖z - w‖ :=
    norm_cauchyGauge_sub_le_sqrt hR hB hA hs hb hsmall z w
  have h1 : ‖(V z - V w) (P z (u z))‖ ≤
      ((kV : ℝ) * ‖z - w‖) * (2 * Cu) := by
    calc
      _ ≤ ‖V z - V w‖ * ‖P z (u z)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((kV : ℝ) * ‖z - w‖) * (2 * Cu) := by
        apply mul_le_mul hVd _ (norm_nonneg _) (by positivity)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hPb z) (hub z hz) (norm_nonneg _) (by norm_num))
  have h2 : ‖V w ((P z - P w) (u z))‖ ≤
      Cv * ((Cg * Real.sqrt ‖z - w‖) * Cu) := by
    calc
      _ ≤ ‖V w‖ * ‖(P z - P w) (u z)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Cv * ((Cg * Real.sqrt ‖z - w‖) * Cu) := by
        apply mul_le_mul (hvb w hw) _ (norm_nonneg _) hCv
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hPd (hub z hz) (norm_nonneg _) (by positivity))
  have h3 : ‖V w (P w (u z - u w))‖ ≤ Cv * (2 * ((ku : ℝ) * ‖z - w‖)) := by
    calc
      _ ≤ ‖V w‖ * ‖P w (u z - u w)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Cv * (2 * ((ku : ℝ) * ‖z - w‖)) := by
        apply mul_le_mul (hvb w hw) _ (norm_nonneg _) hCv
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hPb w) hud (norm_nonneg _) (by norm_num))
  have heq : V z (P z (u z)) - V w (P w (u w)) =
      (V z - V w) (P z (u z)) + V w ((P z - P w) (u z)) + V w (P w (u z - u w)) := by
    simp only [sub_apply, map_sub]
    abel
  change ‖V z (P z (u z)) - V w (P w (u w))‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖(V z - V w) (P z (u z))‖ + ‖V w ((P z - P w) (u z))‖ +
        ‖V w (P w (u z - u w))‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((kV : ℝ) * ‖z - w‖) * (2 * Cu) +
        Cv * ((Cg * Real.sqrt ‖z - w‖) * Cu) +
          Cv * (2 * ((ku : ℝ) * ‖z - w‖)) := add_le_add (add_le_add h1 h2) h3
    _ = ((kV : ℝ) * 2 * Cu + Cv * 2 * ku) * ‖z - w‖ +
        Cv * Cg * Cu * Real.sqrt ‖z - w‖ := by ring
    _ ≤ ((kV : ℝ) * 2 * Cu + Cv * 2 * ku) *
        (Real.sqrt (2 * r) * Real.sqrt ‖z - w‖) +
          Cv * Cg * Cu * Real.sqrt ‖z - w‖ := by
      gcongr
    _ = C * Real.sqrt ‖z - w‖ := by dsimp only [C]; ring

end PoincareConjecture.M65Branch
