import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeakGreen













noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace PoincareConjecture

open M65Interior Proofs.M58







theorem m64HalfDisk_polar_ae {epsilon R H : ℝ}
    (hepsilon : 0 < epsilon) (hRH : R ≤ H) {P : LoopPlane → Prop}
    (hP : ∀ᵐ z ∂volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}), P z) :
    ∀ᵐ r ∂volume.restrict (Icc epsilon R),
      ∀ᵐ theta ∂volume.restrict (Icc (0 : ℝ) Real.pi), P (r • angularPoint theta) := by
  let rho := volume.restrict (Icc epsilon R)
  let nu := volume.restrict (Icc (0 : ℝ) Real.pi)
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  have hK : MeasurableSet K := measurableSet_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hm := (polarPlane_measurePreserving (0 : LoopPlane)).measurable
  have hangle : Icc (0 : ℝ) Real.pi ⊆ Icc (-Real.pi) Real.pi :=
    Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have hdom : Measure.map (polarPlane 0) (rho.prod nu) ≤
      (ENNReal.ofReal epsilon)⁻¹ • (volume : Measure LoopPlane) :=
    (Measure.map_mono (Measure.prod_mono le_rfl
      (Measure.restrict_mono hangle le_rfl)) hm).trans (polarPlane_map_strip_le 0 hepsilon)
  have hall : ∀ᵐ z : LoopPlane ∂volume, z ∈ K → P z := (ae_restrict_iff' hK).mp hP
  have hpull := ae_of_ae_map hm.aemeasurable
    (ae_mono hdom (Measure.ae_smul_measure hall (ENNReal.ofReal epsilon)⁻¹))
  have hmem : ∀ᵐ p ∂rho.prod nu,
      p ∈ Icc epsilon R ×ˢ Icc (0 : ℝ) Real.pi := by
    dsimp only [rho, nu]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  suffices h : ∀ᵐ p ∂rho.prod nu, P (p.1 • angularPoint p.2) from
    Measure.ae_ae_of_ae_prod h
  filter_upwards [hpull, hmem] with p hp hpm
  have hr : 0 ≤ p.1 := hepsilon.le.trans hpm.1.1
  have hz : polarPlane 0 p ∈ K := by
    constructor
    · rw [mem_closedBall_zero_iff]
      simpa only [polarPlane, zero_add, norm_smul, Real.norm_of_nonneg hr,
        norm_angularPoint, mul_one] using hpm.1.2.trans hRH
    · change 0 ≤ (0 + p.1 • angularPoint p.2) 1
      simp only [zero_add, PiLp.smul_apply, smul_eq_mul, angularPoint,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact mul_nonneg hr (Real.sin_nonneg_of_mem_Icc hpm.2)
  simpa only [polarPlane, zero_add] using hp hz

end PoincareConjecture
