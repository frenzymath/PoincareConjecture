import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.ScalarEvolution
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Definitions.M30ControlledBlowupLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

theorem curvatureTensorNorm_eq_of_local_homothety
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y,
      g.inner y v w = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v)
        (mfderiv (𝓡 n) (𝓡 n) f y w))
    {x : M} (hx : x ∈ U) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm (f x) / Q := by
  have hlocal := D.curvatureTensorNorm_eq_of_local_isometry
    (M13.scaleLeviCivitaData D' Q hQ) hU hf hmetric hx
  exact hlocal.trans (M13.homothety_curvatureTensorNorm_eq h
    (M13.scaleSmoothMetric h Q hQ) (Diffeomorph.refl (𝓡 n) N ∞)
    Q hQ (M13.identity_metricHomothety h Q hQ) D'
    (M13.scaleLeviCivitaData D' Q hQ) (f x))

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

private theorem exists_model_curvature_norm_modulus :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (h : RiemannianMetric 3 E3) (Dh : LeviCivitaData h),
      (∀ r : ℕ, r ≤ 2 → ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ r (fun y => h.inner y (roundCylinderEuclideanBasis i)
            (roundCylinderEuclideanBasis j)) 0 -
          iteratedFDeriv ℝ r (fun y => roundCylinderEuclideanMetric.inner y
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ < delta) →
      |Dh.curvatureTensorNorm 0 -
        roundCylinderEuclideanMetric.leviCivitaData.curvatureTensorNorm 0| < 1 := by
  classical
  let g := roundCylinderEuclideanMetric
  let D := g.leviCivitaData
  let Data := (h : RiemannianMetric 3 E3) × LeviCivitaData h
  let J := fun p : Data => p.1.scalarMetricTwoJet 0 roundCylinderEuclideanBasis
  let L := Filter.comap J (𝓝 (g.scalarMetricTwoJet 0 roundCylinderEuclideanBasis))
  have hJ : Tendsto J L (𝓝 (g.scalarMetricTwoJet 0 roundCylinderEuclideanBasis)) :=
    tendsto_comap
  have hjets (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
      Tendsto (fun p : Data => iteratedFDeriv ℝ r
        (fun y => p.1.inner y (roundCylinderEuclideanBasis i)
          (roundCylinderEuclideanBasis j)) 0) L
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (roundCylinderEuclideanBasis i)
          (roundCylinderEuclideanBasis j)) 0)) := by
    let k : Fin 3 := ⟨r, by omega⟩
    exact ((continuous_apply j).tendsto _).comp
      (((continuous_apply i).tendsto _).comp (((continuous_apply k).tendsto _).comp hJ))
  have hnorm := LeviCivitaData.tendsto_curvatureTensorNorm_of_scalar_metric_jets
    (fun p : Data => p.2) D 0 roundCylinderEuclideanBasis hjets
  obtain ⟨delta, hdelta, hbound⟩ := (Metric.nhds_basis_ball.comap J).mem_iff.mp
    (hnorm (Metric.ball_mem_nhds (D.curvatureTensorNorm 0) zero_lt_one))
  refine ⟨delta, hdelta, ?_⟩
  intro h Dh hj
  have hclose : J ⟨h, Dh⟩ ∈ Metric.ball
      (g.scalarMetricTwoJet 0 roundCylinderEuclideanBasis) delta := by
    rw [Metric.mem_ball, dist_pi_lt_iff hdelta]
    intro r
    rw [dist_pi_lt_iff hdelta]
    intro i
    rw [dist_pi_lt_iff hdelta]
    intro j
    simpa only [dist_eq_norm, J, RiemannianMetric.scalarMetricTwoJet] using
      hj r.val (by omega) i j
  simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] using hbound hclose

private theorem metric_scalar_jet_le_full
    (h g : RiemannianMetric 3 E3) (r : ℕ) (i j : Fin 3) :
    ‖iteratedFDeriv ℝ r (fun x => h.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)) 0 -
      iteratedFDeriv ℝ r (fun x => g.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j)) 0‖ ≤
      ‖iteratedFDeriv ℝ r h.euclideanCoefficients 0 -
        iteratedFDeriv ℝ r g.euclideanCoefficients 0‖ := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hs (k : RiemannianMetric 3 E3) : ContDiffAt ℝ ∞
      (fun x => k.inner x (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0 :=
    ((k.contDiffAt_euclideanCoefficients 0).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  rw [← iteratedFDeriv_sub_apply ((hs h).of_le hr) ((hs g).of_le hr),
    ← iteratedFDeriv_sub_apply ((h.contDiffAt_euclideanCoefficients 0).of_le hr)
      ((g.contDiffAt_euclideanCoefficients 0).of_le hr)]
  let B := fun x => h.euclideanCoefficients x - g.euclideanCoefficients x
  have hB : ContDiffAt ℝ ∞ B 0 :=
    (h.contDiffAt_euclideanCoefficients 0).sub (g.contDiffAt_euclideanCoefficients 0)
  have hb (a : Fin 3) : ‖roundCylinderEuclideanBasis a‖ = 1 := by
    simp only [roundCylinderEuclideanBasis, Module.Basis.reindex_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.norm_eq_one]
  have hfirst := norm_iteratedFDeriv_clm_apply_const
    (c := roundCylinderEuclideanBasis i) hB hr
  have hsecond := norm_iteratedFDeriv_clm_apply_const
    (c := roundCylinderEuclideanBasis j)
    (hB.clm_apply (contDiffAt_const (c := roundCylinderEuclideanBasis i))) hr
  simp only [hb, one_mul] at hfirst hsecond
  exact hsecond.trans hfirst

private noncomputable def normRechart {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) :
    E3 ≃L[ℝ] V :=
  (RiemannianMetric.lineModelEquiv 2).symm.trans
    (evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one))

private noncomputable def normRealizationMap
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) : E3 → (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier :=
  fun y => N.time_cylinder.forward tau htau
    (N.coordinate_map ((chartAt E2 q).symm ((0, z) + normRechart htau y).1,
      ((0, z) + normRechart htau y).2))

private theorem normRealizationMap_contMDiffAt
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) {x : E3}
    (hx : ((0, z) + normRechart htau x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (normRealizationMap N htau q z) x := by
  let p : V := (0, z) + normRechart htau x
  let w : RoundCylinderSpace := ((chartAt E2 q).symm p.1, p.2)
  have hmem : N.coordinate_map w ∈ N.carrier := by
    let a : NeckDomain epsilon := (w.1, ⟨w.2, hx⟩)
    simpa only [N.coordinate_map_eq a, a] using (N.coordinate a).property
  have hc := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ w.1, hx⟩)
  have hf := (N.time_cylinder.forward_smooth tau htau).contMDiffAt
    (N.carrier_open.mem_nhds hmem)
  have ha : ContMDiffAt (𝓡 3) 𝓘(ℝ, V) ∞
      (fun y => (0, z) + normRechart htau y) x :=
    (contDiffAt_const.add (normRechart htau).contDiff.contDiffAt).contMDiffAt
  have hchart : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun y => ((chartAt E2 q).symm ((0, z) + normRechart htau y).1,
        ((0, z) + normRechart htau y).2)) x :=
    (cylinderChart_symm_smooth q p).comp x ha
  exact hf.comp x (hc.comp x hchart)

private theorem strongNeck_realization_curvature_norm
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) {z : ℝ} (hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    {h : RiemannianMetric 3 E3} (Dh : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] strongNeckEvolvingCoefficients N htau q z) :
    Dh.curvatureTensorNorm 0 = (1 - tau) *
      F.curvatureNorm (N.time_cylinder.pointMap tau htau (N.coordinate_map (q, z))) /
        (N.scale⁻¹ ^ 2) := by
  let Q := N.scale⁻¹ ^ 2
  let a := 1 - tau
  let f := normRealizationMap N htau q z
  let U : Set E3 := {x | ((0, z) + normRechart htau x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add (normRechart htau).continuous))
  have h0U : 0 ∈ U := by simpa only [U, mem_ofPred_eq, map_zero, add_zero] using hz
  obtain ⟨W, hW, hWo, h0W⟩ := mem_nhds_iff.mp (heq.and (hU.mem_nhds h0U))
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f W := fun x hx =>
    (normRealizationMap_contMDiffAt N htau q z (hW hx).2).contMDiffWithinAt
  have hm : ∀ x ∈ W, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner x v w = (Q / a) * (F.metric (t + tau / Q)).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
    intro x hx v w
    change h.euclideanCoefficients x v w = _
    rw [(hW hx).1]
    rfl
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have ha : 0 < a := by dsimp only [a]; linarith [htau.2]
  have hzero : f 0 = N.time_cylinder.forward tau htau (N.coordinate_map (q, z)) := by
    simp only [f, normRealizationMap, map_zero, add_zero,
      Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero]
  have hnorm := curvatureTensorNorm_eq_of_local_homothety Dh (F.connection (t + tau / Q))
    (div_pos hQ ha) hWo hf hm h0W
  rw [hzero] at hnorm
  change Dh.curvatureTensorNorm 0 = a * (F.connection (t + tau / Q)).curvatureTensorNorm
    (N.time_cylinder.forward tau htau (N.coordinate_map (q, z))) / Q
  rw [hnorm]
  field_simp

theorem exists_strongNeck_backward_curvature_bound :
    ∃ epsilon₀ K : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧ 0 < K ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
        ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ epsilon₀ →
          ∀ {tau : ℝ} (htau : tau ∈ Ioc (-1) 0), ∀ x ∈ N.carrier,
            |F.curvatureNorm (N.time_cylinder.pointMap tau htau x)| ≤ K * (N.scale⁻¹ ^ 2) := by
  obtain ⟨delta, hdelta, hmodulus⟩ := exists_model_curvature_norm_modulus
  obtain ⟨epsilon₀, hpos, hsmall, hrealize⟩ :=
    exists_strongNeck_evolving_fourJet_realization.{u} hdelta
  let m := roundCylinderEuclideanMetric.leviCivitaData.curvatureTensorNorm 0
  let K := |m| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨epsilon₀, K, hpos, hsmall, hK, ?_⟩
  intro F t epsilon N hN tau htau x hx
  let q := (N.coordinate_inverse x).1
  let z := (N.coordinate_inverse x).2
  have hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := N.coordinate_inverse_mem x hx
  have hcoord : N.coordinate_map (q, z) = x := N.coordinate_inverse_right x hx
  obtain ⟨h, Dh, heq, hjets⟩ := hrealize N hN htau q hz
  have hclose := hmodulus h Dh (fun r hr i j =>
    (metric_scalar_jet_le_full h roundCylinderEuclideanMetric r i j).trans_lt
      (hjets r (by omega)))
  have hnorm : |Dh.curvatureTensorNorm 0| < K := by
    have htri := abs_add_le (Dh.curvatureTensorNorm 0 - m) m
    dsimp only [K]
    have hclose' : |Dh.curvatureTensorNorm 0 - m| < 1 := hclose
    have heq' : Dh.curvatureTensorNorm 0 - m + m = Dh.curvatureTensorNorm 0 := by ring
    rw [heq'] at htri
    linarith
  have hscale := strongNeck_realization_curvature_norm N htau q hz Dh heq
  rw [hcoord] at hscale
  have hQ : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have ha : 1 ≤ 1 - tau := by linarith [htau.2]
  rw [hscale, abs_div, abs_mul, abs_of_pos (by linarith : 0 < 1 - tau),
    abs_of_pos hQ] at hnorm
  have hh := (div_lt_iff₀ hQ).mp hnorm
  nlinarith [abs_nonneg (F.curvatureNorm (N.time_cylinder.pointMap tau htau x))]

theorem negativeCurvaturePart_le_of_pinched_scalar_bound
    {F : GeneralizedRicciFlowData.{u}} (hbranch : generalizedPinchedOrNonnegative F)
    {M q eta : ℝ} (hM : 0 < M) (hq : 0 < q) (heta : 0 < eta)
    (hlarge : Real.exp (4 + M / (2 * eta)) / eta ≤ q)
    (p : F.point) (hscalar : F.scalar p ≤ M * q) :
    (F.connection p.1).negativeCurvaturePart p.2 ≤ eta * q := by
  have hp : p.1 ∈ F.interval := (F.slice_nonempty_iff p.1).mp ⟨p.2⟩
  rcases hbranch with ⟨_, hpinch⟩ | hnonneg
  · obtain ⟨_, htime, _, hpinch⟩ := hpinch p.1 hp
    by_contra hnot
    have hnu : eta * q < (F.connection p.1).negativeCurvaturePart p.2 := lt_of_not_ge hnot
    have hnupos : 0 < (F.connection p.1).negativeCurvaturePart p.2 :=
      (mul_pos heta hq).trans hnu
    have hthreshold : Real.exp (4 + M / (2 * eta)) ≤ eta * q := by
      simpa only [mul_comm] using (div_le_iff₀ heta).mp hlarge
    have hlog : 4 + M / (2 * eta) <
        Real.log ((F.connection p.1).negativeCurvaturePart p.2) := by
      have hh := Real.log_lt_log (Real.exp_pos (4 + M / (2 * eta)))
        (hthreshold.trans_lt hnu)
      simpa only [Real.log_exp] using hh
    have hlogtime : 0 ≤ Real.log (1 + p.1) := Real.log_nonneg (by linarith)
    have hweak := hpinch p.2 hnupos
    have hcoef : 0 < M / (2 * eta) := by positivity
    have hprod := mul_lt_mul_of_pos_right hnu hcoef
    have hprod' := mul_lt_mul_of_pos_left
      (show M / (2 * eta) < Real.log ((F.connection p.1).negativeCurvaturePart p.2) - 3
        by linarith) (show 0 < 2 * (F.connection p.1).negativeCurvaturePart p.2 by positivity)
    have hcancel : 2 * (eta * q * (M / (2 * eta))) = M * q := by
      field_simp
    have hdrop : 0 ≤ 2 * (F.connection p.1).negativeCurvaturePart p.2 * Real.log (1 + p.1) :=
      mul_nonneg (by positivity) hlogtime
    nlinarith
  · rw [(hnonneg.1 p.1 hp p.2).2]
    exact (mul_pos heta hq).le

end PoincareConjecture.M32
