import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetRicciDensity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetConformalCurvature
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ActualDiskGauss
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryGlobal













set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold Bundle InnerProductSpace

namespace PoincareConjecture.M65MinimalDisk

open M65Gauss

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

private theorem interior_differential_pairing (S : M65MinimalDisk g connection gamma)
    {x : LoopPlane} (hx : x ∈ ball (0 : LoopPlane) 1) (v w : LoopPlane) :
    g.inner (S.disk.map x) (mfderiv (𝓡 2) (𝓡 3) S.disk.map x v)
      (mfderiv (𝓡 2) (𝓡 3) S.disk.map x w) = S.conformalFactor x * inner ℝ v w := by
  have hmem : loopDiskSet ∈ 𝓝 x :=
    mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
  have hnorm (u : LoopPlane) := S.withinDifferential_inner_self (ball_subset_closedBall hx) u
  simp only [mfderivWithin_of_mem_nhds hmem] at hnorm
  have hsum := hnorm (v + w)
  simp only [map_add, add_apply, hnorm, norm_add_sq_real] at hsum
  have hsym := g.symm (S.disk.map x) (mfderiv (𝓡 2) (𝓡 3) S.disk.map x w)
    (mfderiv (𝓡 2) (𝓡 3) S.disk.map x v)
  linarith

private theorem actual_secondFundamentalForm_symm
    {h : RiemannianMetric 2 LoopPlane} (Ds : LeviCivitaData h)
    (S : M65MinimalDisk g connection gamma)
    {x : LoopPlane} (hx : x ∈ ball (0 : LoopPlane) 1) (u v : LoopPlane) :
    m65PlaneSecondFundamentalForm connection Ds S.disk.map x u v =
      m65PlaneSecondFundamentalForm connection Ds S.disk.map x v u := by
  let p := S.disk.map x
  let c := chartAt LoopAmbient p
  obtain ⟨gE, DE, hE⟩ := m65Exists_chartMetric g p
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] at hE
  have hsrc : S.disk.map x ∈ c.source := mem_chart_source LoopAmbient p
  have hG : ContDiffAt ℝ ∞ (c ∘ S.disk.map) x :=
    contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' hsrc).comp x
      (S.interior_smooth.contMDiffAt (isOpen_ball.mem_nhds hx)))
  rw [m65PlaneSecondFundamentalForm_chart connection Ds DE p isOpen_ball
      S.interior_smooth hx hsrc hE u v,
    m65PlaneSecondFundamentalForm_chart connection Ds DE p isOpen_ball
      S.interior_smooth hx hsrc hE v u,
    secondFundamentalForm_symm DE Ds hG u v]

set_option maxHeartbeats 1800000 in





theorem logarithmicGaussDensity_le_gaussContraction [T2Space M]
    (S : M65MinimalDisk g connection gamma)
    {x : LoopPlane} (hx : x ∈ ball (0 : LoopPlane) 1) (hpos : 0 < S.conformalFactor x) :
    logarithmicGaussDensity S.conformalFactor x ≤
      m65PlaneRicciTraceDensity connection S.disk.map x -
        connection.scalarCurvature (S.disk.map x) * m60AreaDensity g S.disk.map x / 2 := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let lambda := S.conformalFactor
  have hlambda : ContDiffOn ℝ ∞ lambda (ball (0 : LoopPlane) 1) := by
    intro y hy
    let E := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
    have hEy : E.symm y ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      change ‖Complex.orthonormalBasisOneI.repr.symm y‖ < 1
      rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
      exact mem_ball_zero_iff.mp hy
    have hh := S.conformalFactor_complex_contDiffOn.contDiffAt (isOpen_ball.mem_nhds hEy)
    have hreal := E.contDiffAt_comp_iff.mp hh
    simpa only [E.apply_symm_apply] using hreal.contDiffWithinAt (s := ball 0 1)
  let U := ball (0 : LoopPlane) 1 ∩ {y | 0 < lambda y}
  have hU : IsOpen U :=
    hlambda.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hxU : x ∈ U := ⟨hx, hpos⟩
  let delta : LoopPlane →L[ℝ] LoopPlane →L[ℝ] ℝ := innerSL ℝ
  let A := fun y : LoopPlane => lambda y • delta
  have hA : ContDiffOn ℝ ∞ A U :=
    (((ContinuousLinearMap.id ℝ ℝ).smulRight delta).contDiff.comp_contDiffOn
      (hlambda.mono inter_subset_left))
  obtain ⟨h, Ds, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hxU A hA
    (fun y _ v w => by
      change lambda y * inner ℝ v w = lambda y * inner ℝ w v
      rw [real_inner_comm])
    (fun y hy v hv => mul_pos hy.2 (real_inner_self_pos.mpr hv))
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : LoopPlane,
      h.inner y v w = g.inner (S.disk.map y)
        (mfderiv (𝓡 2) (𝓡 3) S.disk.map y v) (mfderiv (𝓡 2) (𝓡 3) S.disk.map y w) := by
    filter_upwards [hV.mem_nhds hxV] with y hy v w
    change h.euclideanCoefficients y v w = _
    rw [heq y hy]
    exact (S.interior_differential_pairing (hVU hy).1 v w).symm
  have hconf (y : LoopPlane) (hy : y ∈ V) (i j : Fin 2) :
      h.euclideanCoefficients y (e i) (e j) = if i = j then lambda y else 0 := by
    rw [heq y hy]
    change lambda y * inner ℝ (e i) (e j) = _
    simp only [e.inner_eq_ite, mul_ite, mul_one, mul_zero]
  have hR := curvatureTensor_conformal_log Ds hV hxV
    (hlambda.mono (hVU.trans inter_subset_left)) (fun y hy => (hVU hy).2) hconf
  have hGauss := m65PlaneSecondFundamentalForm_gauss connection Ds isOpen_ball
    S.interior_smooth hx hmetric (e 0) (e 1) (e 0) (e 1)
  let B := m65PlaneSecondFundamentalForm connection Ds S.disk.map x
  have htrace : B (e 0) (e 0) + B (e 1) (e 1) = 0 := by
    have hh := m65PlaneSecondFundamentalForm_euclideanTrace connection Ds S.disk.map
      (c := lambda) (Filter.Eventually.mono (hV.mem_nhds hxV) fun y hy => hconf y hy)
    rw [S.harmonic x hx, Fin.sum_univ_two] at hh
    exact hh
  have hB11 : B (e 1) (e 1) = -B (e 0) (e 0) := eq_neg_of_add_eq_zero_right htrace
  have hB10 : B (e 1) (e 0) = B (e 0) (e 1) :=
    S.actual_secondFundamentalForm_symm Ds hx (e 1) (e 0)
  have hnonneg (v : TangentSpace (𝓡 3) (S.disk.map x)) : 0 ≤ g.inner (S.disk.map x) v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos _ _ hv).le
  let a := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 3) S.disk.map x (e i)
  have ha (i j : Fin 2) : g.inner (S.disk.map x) (a i) (a j) =
      if i = j then lambda x else 0 := by
    simpa only [S.boundaryColumn_eq_mfderiv hx, a, e, lambda] using
      S.boundaryColumn_inner (ball_subset_closedBall hx) i j
  have hRic := m60Ricci_plane_trace_equal_length connection connection.curvatureTensorCalculus
    (S.disk.map x) (a 0) (a 1) hpos (by simpa using ha 0 0)
      (by simpa using ha 1 1) (by simpa using ha 0 1)
  have hQ : m65PlaneRicciTraceDensity connection S.disk.map x -
      connection.scalarCurvature (S.disk.map x) * m60AreaDensity g S.disk.map x / 2 =
        connection.curvatureTensor (S.disk.map x) (a 0) (a 1) (a 0) (a 1) / lambda x := by
    rw [m65PlaneRicciTraceDensity_eq_sum_of_conformal connection S.disk.map x
      (lambda x) (S.interior_areaGram hx),
      m65AreaDensity_eq_of_conformal g S.disk.map x (lambda x) (S.interior_areaGram hx),
      Fin.sum_univ_two]
    change connection.ricci (S.disk.map x) (a 0) (a 0) +
      connection.ricci (S.disk.map x) (a 1) (a 1) - _ = _
    linarith
  rw [hQ]
  change logarithmicGaussDensity lambda x ≤ _
  change Ds.curvatureTensor x (e 0) (e 1) (e 0) (e 1) / lambda x =
    logarithmicGaussDensity lambda x at hR
  rw [← hR, hGauss]
  change (connection.curvatureTensor (S.disk.map x) (a 0) (a 1) (a 0) (a 1) +
    g.inner (S.disk.map x) (B (e 0) (e 0)) (B (e 1) (e 1)) -
    g.inner (S.disk.map x) (B (e 0) (e 1)) (B (e 1) (e 0))) / lambda x ≤ _
  rw [hB11, hB10, map_neg]
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith [hnonneg (B (e 0) (e 0)), hnonneg (B (e 0) (e 1))]

end PoincareConjecture.M65MinimalDisk
