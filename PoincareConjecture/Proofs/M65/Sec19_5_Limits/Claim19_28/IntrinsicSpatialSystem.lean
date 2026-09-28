import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.SpatialInduction
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateState

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

noncomputable def m65IntrinsicChartField {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (p : M) : ℕ → ℝ → ℝ → EuclideanSpace ℝ (Fin n) × ℝ
  | 0, t, x => ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1, t)
  | j + 1, t, x => (m65ProjectedCoordinateJet P c p j t x,
      (P.flow.metric t).inner (c x t) (m65IntrinsicTangentJet P.flow c j t x)
        (P.charts.circleUnit (c x t)))

noncomputable def m65IntrinsicSpatialOperator (F : RicciFlow n M (Icc a b)) (p : M) :
    (j : ℕ) → (ℝ × (Fin (j + 2) → EuclideanSpace ℝ (Fin n) × ℝ)) →
      EuclideanSpace ℝ (Fin n) × ℝ
  | 0, z => (z.1 • (z.2 1).1, 0)
  | j + 1, z =>
      let q := z.2 ⟨0, by omega⟩
      let S := z.2 ⟨1, by omega⟩
      let Y := z.2 ⟨j + 1, by omega⟩
      let H := z.2 ⟨j + 2, by omega⟩
      (z.1 • H.1 - M04.shiChartChristoffel (F.connection q.2)
        (chartAt (EuclideanSpace ℝ (Fin n)) p) q.1 (z.1 • S.1) Y.1,
        z.1 * H.2)

noncomputable def m65IntrinsicSpeedCoefficient (F : RicciFlow n M (Icc a b)) (p : M)
    (z : Fin 3 → EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  -(m65FlowChartRicci F p ((z 0).2, (z 0).1) (z 1).1 (z 1).1 +
    m65FlowChartMetric F p ((z 0).2, (z 0).1) (z 2).1 (z 2).1 + (z 2).2 ^ 2)

def m65IntrinsicSpatialDomain (p : M) (j : ℕ) :
    Set (ℝ × (Fin (j + 2) → EuclideanSpace ℝ (Fin n) × ℝ)) :=
  {z | (z.2 0).2 ∈ Ioo a b ∧
    (z.2 0).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target}

def m65IntrinsicSpeedDomain (p : M) : Set (Fin 3 → EuclideanSpace ℝ (Fin n) × ℝ) :=
  {z | (z 0).2 ∈ Ioo a b ∧ (z 0).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target}

omit [IsManifold (𝓡 n) ∞ M] in

theorem m65IntrinsicSpatialDomain_isOpen (p : M) (j : ℕ) :
    IsOpen (m65IntrinsicSpatialDomain (n := n) (a := a) (b := b) p j) := by
  exact (isOpen_Ioo.preimage (by fun_prop)).inter
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.preimage (by fun_prop))

omit [IsManifold (𝓡 n) ∞ M] in

theorem m65IntrinsicSpeedDomain_isOpen (p : M) :
    IsOpen (m65IntrinsicSpeedDomain (n := n) (a := a) (b := b) p) := by
  exact (isOpen_Ioo.preimage (by fun_prop)).inter
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.preimage (by fun_prop))

theorem m65IntrinsicSpatialOperator_contDiffOn [T2Space M] (p : M) (j : ℕ) :
    ContDiffOn ℝ ∞ (m65IntrinsicSpatialOperator F p j)
      (m65IntrinsicSpatialDomain (a := a) (b := b) p j) := by
  cases j with
  | zero =>
    have h : ContDiff ℝ ∞ (m65IntrinsicSpatialOperator F p 0) := by
      unfold m65IntrinsicSpatialOperator
      fun_prop
    exact h.contDiffOn
  | succ j =>
    intro z hz
    have hparam : ContDiffAt ℝ ∞
        (fun w : ℝ × (Fin (j + 1 + 2) → EuclideanSpace ℝ (Fin n) × ℝ) =>
          ((w.2 0).2, (w.2 0).1)) z := by fun_prop
    have hGamma := (M62.flow_chartChristoffel_smooth F p).contDiffAt
      (prod_mem_nhds (Icc_mem_nhds hz.1.1 hz.1.2)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.mem_nhds hz.2))
    have hcoeff := hGamma.comp (f := fun w :
      ℝ × (Fin (j + 1 + 2) → EuclideanSpace ℝ (Fin n) × ℝ) =>
        ((w.2 0).2, (w.2 0).1)) z hparam
    apply ContDiffAt.contDiffWithinAt
    unfold m65IntrinsicSpatialOperator
    dsimp only
    fun_prop

theorem m65IntrinsicSpeedCoefficient_contDiffOn (p : M) :
    ContDiffOn ℝ ∞ (m65IntrinsicSpeedCoefficient F p)
      (m65IntrinsicSpeedDomain (a := a) (b := b) p) := by
  intro z hz
  have hparam : ContDiffAt ℝ ∞
      (fun w : Fin 3 → EuclideanSpace ℝ (Fin n) × ℝ => ((w 0).2, (w 0).1)) z := by
    fun_prop
  have hnear := (isOpen_Ioo.prod (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target).mem_nhds
    (show ((z 0).2, (z 0).1) ∈ Ioo a b ×ˢ
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target from hz)
  have hmetric := ((m65FlowChartMetric_contDiffOn F p).contDiffAt hnear).comp z hparam
  have hricci := ((m65FlowChartRicci_contDiffOn F p).contDiffAt hnear).comp z hparam
  apply ContDiffAt.contDiffWithinAt
  unfold m65IntrinsicSpeedCoefficient
  fun_prop

theorem m65IntrinsicChartField_contDiffAt [T2Space M] {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) (j : ℕ) {t x : ℝ}
    (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    ContDiffAt ℝ ∞ (m65IntrinsicChartField P c p j t) x := by
  let := P.charts.chartedSpace
  have hbase : Continuous (fun y => (c y t).1) :=
    continuous_fst.comp (hc.spatial_regular t (Ioo_subset_Icc_self ht)).continuous
  have hU := (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.preimage hbase
  cases j with
  | zero =>
    have hpos := (m65ProjectedChartState_contDiffAt P c hc p ht hx).snd.fst
    exact (hpos.comp x (contDiffAt_const.prodMk contDiffAt_id)).prodMk contDiffAt_const
  | succ j =>
    have hhorizontal :=
      ((Proofs.M09.tangentChartPhase_contMDiffOn p).comp
        (m65ProjectedTangentJet_spatial_contMDiff P c hc ht j).contMDiffOn
        (fun y (hy : y ∈ (fun y => (c y t).1) ⁻¹'
          (chartAt (EuclideanSpace ℝ (Fin n)) p).source) => hy)).contDiffOn.snd
    have hfield := m65IntrinsicTangentJet_joint_contMDiff c hc j
    have hunit :=
      (M62.circleProduct_identities P).circle_unit_smooth.comp_contMDiffOn hc.joint_smooth
    have hvertical := (M62.metric_pairing_contDiffOn P.flow c hc.joint_smooth
      (fun z => m65IntrinsicTangentJet P.flow c j z.2 z.1)
      (fun z => P.charts.circleUnit (c z.1 z.2)) hfield hunit).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
    exact (hhorizontal.contDiffAt (hU.mem_nhds hx)).prodMk hvertical.contDiffAt

theorem m65ActualVerticalJet_hasDerivAt [T2Space M] {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {t : ℝ} (ht : t ∈ Ioo a b) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (P.flow.metric t).inner (c y t)
      (m65IntrinsicTangentJet P.flow c j t y) (P.charts.circleUnit (c y t)))
      (curveSpeed P.flow c t x * (P.flow.metric t).inner (c x t)
        (m65IntrinsicTangentJet P.flow c (j + 1) t x) (P.charts.circleUnit (c x t))) x := by
  let := P.charts.chartedSpace
  have hP := M62.circleProduct_identities P
  have hcurve := (hc.spatial_regular t (Ioo_subset_Icc_self ht) x).mdifferentiableAt (by norm_num)
  have hunit := (hP.circle_unit_smooth (c x t)).mdifferentiableAt (by simp)
  have hjet : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
      (fun y => (⟨c y t, m65IntrinsicTangentJet P.flow c j t y⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point)) x := by
    simpa only [Function.comp_def, id_eq] using
      ((m65IntrinsicTangentJet_joint_contMDiff c hc j).comp_contMDiff
        (contDiff_id.prodMk contDiff_const).contMDiff
        (fun _ => ⟨mem_univ _, ht⟩)).mdifferentiableAt (by simp) (x := x)
  have hparallel : rampHorizontalCovariantDerivative (P.flow.connection t)
      (fun y => c y t) (fun y => P.charts.circleUnit (c y t)) x = 0 := by
    rw [M62.pullback_ambient_field (P.flow.connection t) hcurve P.charts.circleUnit hunit]
    exact hP.circle_parallel t (c x t) _
  have hp := M62.hasDerivAt_metric_pairing (P.flow.connection t) hcurve hjet (hunit.comp x hcurve)
  apply hp.congr_deriv
  rw [hparallel, m65IntrinsicTangentJet_pullback c hc (Ioo_subset_Icc_self ht)]
  simp only [map_zero, add_zero, map_smul, smul_apply, smul_eq_mul]

theorem m65IntrinsicChartField_hasDerivAt [T2Space M] {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) (j : ℕ) {t x : ℝ}
    (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (m65IntrinsicChartField P c p j t)
      (m65IntrinsicSpatialOperator F p j
        (curveSpeed P.flow c t x, fun l => m65IntrinsicChartField P c p l t x)) x := by
  cases j with
  | zero =>
    exact (m65ProjectedCoordinates_hasDerivAt P c hc p (Ioo_subset_Icc_self ht) hx).prodMk
      (hasDerivAt_const x t)
  | succ j =>
    exact (m65ProjectedCoordinateJet_hasDerivAt P c hc p ht hx j).prodMk
      (m65ActualVerticalJet_hasDerivAt P c hc ht j x)

theorem m65IntrinsicSpeedCoefficient_eq {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65IntrinsicSpeedCoefficient F p (fun l => m65IntrinsicChartField P c p l t x) =
      -(m62TangentRicci P.flow c t x + m62CurvatureSquared P.flow c t x) := by
  unfold m65IntrinsicSpeedCoefficient
  dsimp only [m65IntrinsicChartField]
  change -(m65FlowChartRicci F p _
    (mfderiv (𝓡 n) (𝓡 n) _ _ (P.charts.split _ (spatialUnitTangent P.flow c t x)).1)
    (mfderiv (𝓡 n) (𝓡 n) _ _ (P.charts.split _ (spatialUnitTangent P.flow c t x)).1) +
    m65FlowChartMetric F p _
      (mfderiv (𝓡 n) (𝓡 n) _ _ (P.charts.split _ (m62CurvatureVector P.flow c t x)).1)
      (mfderiv (𝓡 n) (𝓡 n) _ _ (P.charts.split _ (m62CurvatureVector P.flow c t x)).1) +
    ((P.flow.metric t).inner _ (m62CurvatureVector P.flow c t x) (P.charts.circleUnit _)) ^ 2) = _
  rw [m65FlowChartRicci_at_source F p ht hx, m65FlowChartMetric_at_source F p t hx]
  exact congrArg Neg.neg (m65NormalizationCoefficient_product_split P c t x).symm

end PoincareConjecture
