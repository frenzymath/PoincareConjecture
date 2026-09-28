import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateCoefficient

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

abbrev M65ProjectedChartStateSpace (n : ℕ) :=
  ℝ × (EuclideanSpace ℝ (Fin n) × (ℝ × ℝ))

abbrev M65ProjectedChartJetSpace (n : ℕ) :=
  M65ProjectedChartStateSpace n × M65ProjectedChartStateSpace n ×
    M65ProjectedChartStateSpace n

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (p : M)

def m65ProjectedChartOperatorDomain : Set (M65ProjectedChartJetSpace n) :=
  {z | z.1.1 ∈ Ioo a b ∧
    z.1.2.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧ 0 < z.1.2.2.1}

noncomputable def m65ChartHorizontalCurvature (z : M65ProjectedChartJetSpace n) :
    EuclideanSpace ℝ (Fin n) :=
  (z.1.2.2.1 ^ 2)⁻¹ •
    (z.2.2.2.1 + M04.shiChartChristoffel (F.connection z.1.1)
      (chartAt (EuclideanSpace ℝ (Fin n)) p) z.1.2.1 z.2.1.2.1 z.2.1.2.1) -
    (z.2.1.2.2.1 / z.1.2.2.1 ^ 3) • z.2.1.2.1

noncomputable def m65ChartNormalization (z : M65ProjectedChartJetSpace n) : ℝ :=
  m65FlowChartRicci F p (z.1.1, z.1.2.1)
      ((z.1.2.2.1)⁻¹ • z.2.1.2.1) ((z.1.2.2.1)⁻¹ • z.2.1.2.1) +
    m65FlowChartMetric F p (z.1.1, z.1.2.1)
      (m65ChartHorizontalCurvature F p z) (m65ChartHorizontalCurvature F p z) +
    (z.2.1.2.2.2 / z.1.2.2.1) ^ 2

noncomputable def m65ProjectedChartOperator (z : M65ProjectedChartJetSpace n) :
    M65ProjectedChartStateSpace n :=
  (1, (m65ChartHorizontalCurvature F p z,
    (-m65ChartNormalization F p z * z.1.2.2.1,
      z.2.2.2.2.2 / z.1.2.2.1 ^ 2 -
        z.2.1.2.2.1 * z.2.1.2.2.2 / z.1.2.2.1 ^ 3 +
        m65ChartNormalization F p z * z.1.2.2.2)))

omit [IsManifold (𝓡 n) ∞ M] in

theorem m65ProjectedChartOperatorDomain_isOpen :
    IsOpen (m65ProjectedChartOperatorDomain (n := n) (a := a) (b := b) p) := by
  apply IsOpen.inter
  · exact isOpen_Ioo.preimage (continuous_fst.comp continuous_fst)
  · apply IsOpen.inter
    · exact (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.preimage (by fun_prop)
    · exact isOpen_lt continuous_const
        (show Continuous (fun z : M65ProjectedChartJetSpace n => z.1.2.2.1) by fun_prop)

theorem m65ChartHorizontalCurvature_contDiffOn [T2Space M] :
    ContDiffOn ℝ ∞ (m65ChartHorizontalCurvature F p)
      (m65ProjectedChartOperatorDomain (a := a) (b := b) p) := by
  intro z hz
  have hpos : z.1.2.2.1 ≠ 0 := ne_of_gt hz.2.2
  have hpos2 : z.1.2.2.1 ^ 2 ≠ 0 := pow_ne_zero 2 hpos
  have hpos3 : z.1.2.2.1 ^ 3 ≠ 0 := pow_ne_zero 3 hpos
  have hparam : ContDiffAt ℝ ∞
      (fun w : M65ProjectedChartJetSpace n => (w.1.1, w.1.2.1)) z := by fun_prop
  have hcoeff : ContDiffAt ℝ ∞
      (fun w : M65ProjectedChartJetSpace n => M04.shiChartChristoffel (F.connection w.1.1)
        (chartAt (EuclideanSpace ℝ (Fin n)) p) w.1.2.1) z := by
    have hGamma := (M62.flow_chartChristoffel_smooth F p).contDiffAt
      (prod_mem_nhds (Icc_mem_nhds hz.1.1 hz.1.2)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.mem_nhds hz.2.1))
    exact hGamma.comp (f := fun w : M65ProjectedChartJetSpace n =>
      (w.1.1, w.1.2.1)) z hparam
  apply ContDiffAt.contDiffWithinAt
  unfold m65ChartHorizontalCurvature
  fun_prop

theorem m65ChartNormalization_contDiffOn [T2Space M] :
    ContDiffOn ℝ ∞ (m65ChartNormalization F p)
      (m65ProjectedChartOperatorDomain (a := a) (b := b) p) := by
  intro z hz
  have hopen := m65ProjectedChartOperatorDomain_isOpen (n := n) (a := a) (b := b) p
  have hpos : z.1.2.2.1 ≠ 0 := ne_of_gt hz.2.2
  have hparam : ContDiffAt ℝ ∞
      (fun w : M65ProjectedChartJetSpace n => (w.1.1, w.1.2.1)) z := by fun_prop
  have hm : ContDiffAt ℝ ∞
      (fun w : M65ProjectedChartJetSpace n => m65FlowChartMetric F p (w.1.1, w.1.2.1)) z := by
    exact ((m65FlowChartMetric_contDiffOn F p).contDiffAt
      ((isOpen_Ioo.prod (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target).mem_nhds
        ⟨hz.1, hz.2.1⟩)).comp z hparam
  have hr : ContDiffAt ℝ ∞
      (fun w : M65ProjectedChartJetSpace n => m65FlowChartRicci F p (w.1.1, w.1.2.1)) z := by
    exact ((m65FlowChartRicci_contDiffOn F p).contDiffAt
      ((isOpen_Ioo.prod (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target).mem_nhds
        ⟨hz.1, hz.2.1⟩)).comp z hparam
  have hcurv := (m65ChartHorizontalCurvature_contDiffOn F p).contDiffAt (hopen.mem_nhds hz)
  apply ContDiffAt.contDiffWithinAt
  unfold m65ChartNormalization
  fun_prop

theorem m65ProjectedChartOperator_contDiffOn [T2Space M] :
    ContDiffOn ℝ ∞ (m65ProjectedChartOperator F p)
      (m65ProjectedChartOperatorDomain (a := a) (b := b) p) := by
  intro z hz
  have hopen := m65ProjectedChartOperatorDomain_isOpen (n := n) (a := a) (b := b) p
  have hpos : z.1.2.2.1 ≠ 0 := ne_of_gt hz.2.2
  have hpos2 : z.1.2.2.1 ^ 2 ≠ 0 := pow_ne_zero 2 hpos
  have hpos3 : z.1.2.2.1 ^ 3 ≠ 0 := pow_ne_zero 3 hpos
  have hcurv := (m65ChartHorizontalCurvature_contDiffOn F p).contDiffAt (hopen.mem_nhds hz)
  have hnorm := (m65ChartNormalization_contDiffOn F p).contDiffAt (hopen.mem_nhds hz)
  apply ContDiffAt.contDiffWithinAt
  unfold m65ProjectedChartOperator
  fun_prop

end PoincareConjecture
