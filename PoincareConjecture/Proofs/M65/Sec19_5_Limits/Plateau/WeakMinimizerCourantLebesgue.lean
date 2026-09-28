import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCrosscutACL
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityOscillation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace PoincareConjecture

open M65Interior

private theorem m65Polar_weighted_strip (g : LoopPlane → ℝ)
    (hg : Integrable g) (hg0 : ∀ z, 0 ≤ g z) (x : LoopPlane)
    {ε R : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ => p.1 * g (polarPlane x p))
      ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) ∧
    (∫ r in Icc ε R, ∫ t in Icc (-Real.pi) Real.pi,
      r * g (polarPlane x (r, t))) ≤ ∫ z, g z := by
  let K := Icc ε R ×ˢ Ioo (-Real.pi) Real.pi
  have hK : MeasurableSet K := measurableSet_Icc.prod measurableSet_Ioo
  have hKU : K ⊆ polarCoord.target := fun p hp => ⟨hε.trans_le hp.1.1, hp.2⟩
  have hstrip :
      (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi)) =
        volume.restrict K := by
    rw [Measure.prod_restrict]
    exact Measure.restrict_congr_set
      (Measure.set_prod_ae_eq (EventuallyEq.refl _ _)
        (Ioo_ae_eq_Icc (α := ℝ) (μ := volume)).symm)
  have hp : Integrable (fun p => g (polarPlane x p)) polarMeasure :=
    (polarPlane_measurePreserving x).integrable_comp_of_integrable hg
  have hw : IntegrableOn (fun p : ℝ × ℝ => p.1 * g (polarPlane x p))
      polarCoord.target := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (measurable_fst.ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hp
    apply h.congr
    filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    simp only [ENNReal.toReal_ofReal hp.1.le, smul_eq_mul]
  have hi : Integrable (fun p : ℝ × ℝ => p.1 * g (polarPlane x p))
      ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [hstrip]
    exact hw.mono_set hKU
  refine ⟨hi, ?_⟩
  rw [← integral_prod _ hi, hstrip]
  calc
    _ ≤ ∫ p in polarCoord.target, p.1 * g (polarPlane x p) := by
      apply setIntegral_mono_set hw
      · filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
        exact mul_nonneg hp.1.le (hg0 _)
      · exact ae_of_all _ (fun p hp => hKU hp)
    _ = ∫ z, g z := by
      have h : (∫ p, g (polarPlane x p) ∂polarMeasure) = ∫ z, g z := by
        have hm := polarPlane_measurePreserving x
        have hg' : AEStronglyMeasurable g (Measure.map (polarPlane x) polarMeasure) :=
          hm.map_eq.symm ▸ hg.aestronglyMeasurable
        exact (integral_map hm.measurable.aemeasurable hg').symm.trans
          (by rw [hm.map_eq])
      rw [polarMeasure, integral_withDensity_eq_integral_toReal_smul
        measurable_fst.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at h
      rw [← h]
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      simp only [ENNReal.toReal_ofReal hp.1.le, smul_eq_mul]

private theorem m65Crosscut_energy_bound
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b))
    {ε R : ℝ} (hε : 0 < ε) (hR : R ≤ 1) :
    ∃ A : ℝ → ℝ, IntegrableOn A (Icc ε R) ∧
      (∫ r in Icc ε R, A r) ≤ ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 ∧
      ∀ᵐ r ∂volume.restrict (Icc ε R),
        (b (Proofs.M58.angularPoint (2 * m65CrosscutAngle r)) -
          b (Proofs.M58.angularPoint (-(2 * m65CrosscutAngle r)))) ^ 2 ≤
            2 * Real.pi * r * A r := by
  classical
  let g : LoopPlane → ℝ := loopDiskSet.indicator (fun z => (d 0 z) ^ 2 + (d 1 z) ^ 2)
  let x : LoopPlane := -EuclideanSpace.basisFun (Fin 2) ℝ 0
  have hd0 := (Lp.memLp (d 0)).integrable_sq
  have hd1 := (Lp.memLp (d 1)).integrable_sq
  have hg : Integrable g := IntegrableOn.integrable_indicator
    (show IntegrableOn (fun z => (d 0 z) ^ 2 + (d 1 z) ^ 2) loopDiskSet volume from hd0.add hd1)
    (show MeasurableSet loopDiskSet from measurableSet_closedBall)
  have hg0 (z : LoopPlane) : 0 ≤ g z := by
    exact indicator_nonneg (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) z
  have hge : (∫ z, g z) = ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 := by
    rw [show g = loopDiskSet.indicator (fun z => (d 0 z) ^ 2 + (d 1 z) ^ 2) from rfl,
      integral_indicator (s := loopDiskSet) measurableSet_closedBall, integral_add hd0 hd1,
      Lp.norm_sq_eq_integral_norm_sq, Lp.norm_sq_eq_integral_norm_sq]
    simp only [Real.norm_eq_abs, sq_abs]
  obtain ⟨hprod, hbudget⟩ := m65Polar_weighted_strip g hg hg0 x hε
  let A (r : ℝ) := ∫ t in Icc (-Real.pi) Real.pi, r * g (polarPlane x (r, t))
  refine ⟨A, hprod.integral_prod_left, hbudget.trans_eq hge, ?_⟩
  filter_upwards [m65WeakTrace_crosscut_AC htrace hε hR, hprod.prod_right_ae,
    ae_restrict_mem measurableSet_Icc] with r hr hgr hrange
  obtain ⟨v, _, _, hJ, hinc, hn, hp⟩ := hr
  have hrpos : 0 < r := hε.trans_le hrange.1
  have hr1 : r ≤ 1 := hrange.2.trans hR
  let c := m65CrosscutAngle r
  let J (t : ℝ) := -r * Real.sin t * d 0 (polarPlane x (r, t)) +
    r * Real.cos t * d 1 (polarPlane x (r, t))
  have hc0 : 0 ≤ c := Real.arccos_nonneg _
  have hcpi : c ≤ Real.pi := Real.arccos_le_pi _
  have hab : -c ≤ c := by linarith
  have hsub : Icc (-c) c ⊆ Icc (-Real.pi) Real.pi := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgfull : IntegrableOn (fun t => g (polarPlane x (r, t)))
      (Icc (-Real.pi) Real.pi) := by
    have h := hgr.const_mul r⁻¹
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul] using h
  have hginner := hgfull.mono_set hsub
  have hJle : (∫ t in Icc (-c) c, J t ^ 2) ≤
      r ^ 2 * ∫ t in Icc (-Real.pi) Real.pi, g (polarPlane x (r, t)) := by
    calc
      _ ≤ ∫ t in Icc (-c) c, r ^ 2 * g (polarPlane x (r, t)) := by
        apply integral_mono_ae hJ.integrable_sq (hginner.const_mul (r ^ 2))
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have hmem := m65Crosscut_mem_disk hrpos hr1 ht
        have he : g (polarPlane x (r, t)) =
            (d 0 (polarPlane x (r, t))) ^ 2 + (d 1 (polarPlane x (r, t))) ^ 2 :=
          indicator_of_mem hmem _
        rw [he]
        simpa only [J, smul_eq_mul, Real.norm_eq_abs, sq_abs] using
          angular_field_norm_sq_le (d 0 (polarPlane x (r, t)))
            (d 1 (polarPlane x (r, t))) r t
      _ = r ^ 2 * ∫ t in Icc (-c) c, g (polarPlane x (r, t)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hgfull (ae_of_all _ (fun t => hg0 _))
          (ae_of_all _ (fun _ ht => hsub ht))) (sq_nonneg r)
  have hosc := interval_increment_norm_sq_le hab hJ hinc
    (-c) ⟨le_rfl, hab⟩ c ⟨hab, le_rfl⟩
  rw [hn, hp] at hosc
  simp only [Real.norm_eq_abs, sq_abs] at hosc
  have hnonneg : 0 ≤ r ^ 2 *
      ∫ t in Icc (-Real.pi) Real.pi, g (polarPlane x (r, t)) := by
    exact mul_nonneg (sq_nonneg r) (integral_nonneg (fun _ => hg0 _))
  calc
    _ ≤ (c - -c) * ∫ t in Icc (-c) c, J t ^ 2 := hosc
    _ ≤ (c - -c) * (r ^ 2 * ∫ t in Icc (-Real.pi) Real.pi,
        g (polarPlane x (r, t))) :=
      mul_le_mul_of_nonneg_left hJle (sub_nonneg.mpr hab)
    _ ≤ (2 * Real.pi) * (r ^ 2 * ∫ t in Icc (-Real.pi) Real.pi,
        g (polarPlane x (r, t))) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ = 2 * Real.pi * r * A r := by
      dsimp only [A]
      rw [integral_const_mul]
      ring

private theorem m65Logarithmic_radius_choice {ε R η : ℝ}
    (hε : 0 < ε) (hεR : ε < R) (A gap : ℝ → ℝ)
    (hA : IntegrableOn A (Icc ε R))
    (hgap : ∀ᵐ r ∂volume.restrict (Icc ε R), gap r ≤ 2 * Real.pi * r * A r)
    (hbudget : 2 * Real.pi * (∫ r in Icc ε R, A r) < η ^ 2 * Real.log (R / ε))
    (P : ℝ → Prop) (hP : ∀ᵐ r ∂volume.restrict (Icc ε R), P r) :
    ∃ r ∈ Icc ε R, P r ∧ gap r < η ^ 2 := by
  by_contra! hno
  have hInv : IntegrableOn (fun r : ℝ => r⁻¹) (Icc ε R) :=
    (continuousOn_id.inv₀ (fun r hr => (hε.trans_le hr.1).ne')).integrableOn_compact isCompact_Icc
  have hlog : (∫ r in Icc ε R, r⁻¹) = Real.log (R / ε) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hεR.le]
    exact integral_inv_of_pos hε (hε.trans hεR)
  have hlow : (η ^ 2 / (2 * Real.pi)) * Real.log (R / ε) ≤
      ∫ r in Icc ε R, A r := by
    rw [← hlog, ← integral_const_mul]
    apply integral_mono_ae (hInv.const_mul _) hA
    filter_upwards [hgap, hP, ae_restrict_mem measurableSet_Icc] with r hr hp hm
    have hrpos : 0 < r := hε.trans_le hm.1
    have hbound : η ^ 2 ≤ 2 * Real.pi * r * A r := (hno r hm hp).trans hr
    have hdiv : η ^ 2 / (2 * Real.pi * r) ≤ A r :=
      (div_le_iff₀ (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hrpos)).mpr
        (by nlinarith only [hbound])
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hdiv
  have hmul := mul_le_mul_of_nonneg_left hlow
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
  have heq : 2 * Real.pi * (η ^ 2 / (2 * Real.pi) * Real.log (R / ε)) =
      η ^ 2 * Real.log (R / ε) := by field_simp
  rw [heq] at hmul
  exact (not_le_of_gt hbudget) hmul

theorem m65WeakTrace_courantLebesgue {ι : Type*} [Fintype ι]
    (u : ι → Lp ℝ 2 (volume.restrict loopDiskSet))
    (d : ι → Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (b : ι → Lp ℝ 2 m65CircleBoundaryMeasure)
    (htrace : ∀ j, M65DiskWeakTrace (u j) (d j) (m65CircleBoundaryPullback (b j)))
    {ε R η : ℝ} (hε : 0 < ε) (hεR : ε < R) (hR : R ≤ 1)
    (hbudget : 2 * Real.pi * (∑ j, (‖d j 0‖ ^ 2 + ‖d j 1‖ ^ 2)) <
      η ^ 2 * Real.log (R / ε))
    (P : ℝ → Prop) (hP : ∀ᵐ r ∂volume.restrict (Icc ε R), P r) :
    ∃ r ∈ Icc ε R, P r ∧
      (∑ j, (b j (Proofs.M58.angularPoint (2 * m65CrosscutAngle r)) -
        b j (Proofs.M58.angularPoint (-(2 * m65CrosscutAngle r)))) ^ 2) < η ^ 2 := by
  choose A hAi hAb hAg using fun j => m65Crosscut_energy_bound (htrace j) hε hR
  let total (r : ℝ) := ∑ j, A j r
  have htotal : IntegrableOn total (Icc ε R) :=
    integrable_finsetSum Finset.univ (fun j _ => hAi j)
  have htotalBound : (∫ r in Icc ε R, total r) ≤
      ∑ j, (‖d j 0‖ ^ 2 + ‖d j 1‖ ^ 2) := by
    rw [show total = fun r => ∑ j, A j r from rfl,
      integral_finsetSum _ (fun j _ => hAi j)]
    exact Finset.sum_le_sum (fun j _ => hAb j)
  apply m65Logarithmic_radius_choice hε hεR total _ htotal ?_
    ((mul_le_mul_of_nonneg_left htotalBound
      (mul_nonneg (by norm_num) Real.pi_pos.le)).trans_lt hbudget) P hP
  filter_upwards [ae_all_iff.mpr hAg] with r hr
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hr j)
  simpa only [← Finset.mul_sum, total] using h

end PoincareConjecture
