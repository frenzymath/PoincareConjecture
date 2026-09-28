import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ManifoldComparison









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open ConnectionVariation ConnectionAlongCurve

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_open_radial_variation_domain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {v : E} (hv : v ∈ Metric.ball 0 R) (w : E) :
    ∃ S : Set ℝ, ∃ a : ℝ, IsOpen S ∧ (0 : ℝ) ∈ S ∧ 1 < a ∧
      (∀ s ∈ S, v + s • w ∈ Metric.ball 0 R) ∧
      ∀ s ∈ S, ∀ t ∈ Ioo (-a) a, t • (v + s • w) ∈ Metric.ball 0 R := by
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hvR) ‖v‖
  let a := 1 + δ
  let S : Set ℝ := {s | a * ‖v + s • w‖ < R}
  have ha : 1 < a := by dsimp [a]; linarith
  have hS : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℝ) ∈ S := by
    simp only [S, mem_ofPred_eq, zero_smul, add_zero]
    dsimp [a]
    nlinarith
  refine ⟨S, a, hS, h0, ha, ?_, ?_⟩
  · intro s hs
    rw [Metric.mem_ball, dist_zero_right]
    exact (le_mul_of_one_le_left (norm_nonneg _) ha.le).trans_lt hs
  · intro s hs t ht
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (abs_lt.mpr ht).le (norm_nonneg _)).trans_lt hs


theorem radialVariation_contDiffAt_chartField
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (v w : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t • v ∈ U) :
    let γ : ℝ → M := fun s => e (s • v)
    let J : (s : ℝ) → TangentSpace (𝓡 n) (γ s) :=
      fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (s • (v + r • w))) 0 1
    ContDiffAt ℝ ∞ (chartField γ (γ t) J) t := by
  dsimp only
  let c := extChartAt (𝓡 n) (e (t • v))
  let q := c ∘ e
  let V : ℝ → EuclideanSpace ℝ (Fin n) := fun s => s • fderiv ℝ q (s • v) w
  have het := he.contMDiffAt (hU.mem_nhds ht)
  have hq : ContDiffAt ℝ ∞ q (t • v) :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (mem_chart_source _ _)).comp (t • v) het)
  have hV : ContDiffAt ℝ ∞ V t := by
    change ContDiffAt ℝ ∞ (fun s : ℝ => s • fderiv ℝ q (s • v) w) t
    apply contDiffAt_id.smul
    have hF : ContDiffAt ℝ ∞ (fun x => fderiv ℝ q x w) (t • v) :=
      (hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    exact hF.comp (f := fun s : ℝ => s • v) t (by fun_prop)
  have hline : Continuous (fun s : ℝ => s • v) := by fun_prop
  have hnear : ∀ᶠ s : ℝ in 𝓝 t,
      s • v ∈ U ∧ e (s • v) ∈ c.source := by
    change (fun s : ℝ => s • v) ⁻¹' (U ∩ e ⁻¹' c.source) ∈ 𝓝 t
    apply hline.continuousAt.preimage_mem_nhds
    exact inter_mem (hU.mem_nhds ht)
      (het.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓡 n) (e (t • v))).mem_nhds
          (mem_extChartAt_source _)))
  apply hV.congr_of_eventuallyEq
  filter_upwards [hnear] with s hs
  have hes := (he.contMDiffAt (hU.mem_nhds hs.1)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp (s • v)
    (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using hs.2)) hes
  rw [mfderiv_eq_fderiv] at hd
  change mfderiv (𝓡 n) (𝓡 n) c (e (s • v))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (s • (v + r • w))) 0 1) = _
  rw [radialVariation_field_eq v w s hes]
  have hd1 := congrArg (fun L => L (s • w)) hd
  change fderiv ℝ q (s • v) (s • w) =
    mfderiv (𝓡 n) (𝓡 n) c (e (s • v))
      (mfderiv (𝓡 n) (𝓡 n) e (s • v) (s • w)) at hd1
  rw [← hd1]
  exact map_smul _ _ _

set_option maxHeartbeats 1000000 in


theorem pullbackCoefficients_zero_of_normalized_chart
    (g : RiemannianMetric n M) {p : M}
    {e : EuclideanSpace ℝ (Fin n) → M}
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) :
    ∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w := by
  subst p
  intro v w
  have hd := mfderiv_comp 0 (mdifferentiableAt_extChartAt (mem_chart_source _ _))
    (he.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ (fun v => extChartAt (𝓡 n) (e 0) (e v)) 0 = _ at hd
  rw [hed.fderiv] at hd
  have hv : L v = mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (e 0)) (e 0)
      (mfderiv (𝓡 n) (𝓡 n) e 0 v) := congrArg (fun A => A v) hd
  have hw : L w = mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (e 0)) (e 0)
      (mfderiv (𝓡 n) (𝓡 n) e 0 w) := congrArg (fun A => A w) hd
  have hm := chartField_inner g (q := fun _ : ℝ => e 0)
    (fun _ => mfderiv (𝓡 n) (𝓡 n) e 0 v)
    (fun _ => mfderiv (𝓡 n) (𝓡 n) e 0 w)
    (t := 0) (mem_extChartAt_source (e 0))
  change g.pullbackCoefficients (extChartAt (𝓡 n) (e 0)).symm
    (extChartAt (𝓡 n) (e 0) (e 0))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (e 0)) (e 0)
      (mfderiv (𝓡 n) (𝓡 n) e 0 v))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (e 0)) (e 0)
      (mfderiv (𝓡 n) (𝓡 n) e 0 w)) = g.pullbackCoefficients e 0 v w at hm
  rw [← hv, ← hw] at hm
  exact hm.symm.trans (hL v w)




theorem radial_geodesic_differential_two_sided
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {R K : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ u w, g.pullbackCoefficients e 0 u w = inner ℝ u w)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (e (t • v)) ≤ K)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖)
    (hsmall : (K * ‖v‖ ^ 2) * Real.exp (max 1 (K * ‖v‖ ^ 2)) ≤ 3)
    (w : EuclideanSpace ℝ (Fin n)) :
    ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
      g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤ 3 * ‖w‖ / 2 := by
  let γ : ℝ → M := fun t => e (t • v)
  let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
  obtain ⟨S, a, hS, h0, ha, hvelocity, hdomain⟩ :=
    exists_open_radial_variation_domain hv w
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-a) a := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => e (z.2 • (v + z.1 • w))) (S ×ˢ Ioo (-a) a) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact fun z hz => hdomain z.1 hz.1 z.2 hz.2
  have hvariation : ∀ s ∈ S,
      g.IsGeodesicOn (fun t : ℝ => e (t • (v + s • w))) (Ioo (-a) a) := by
    intro s hs t ht
    exact hgeo _ (hvelocity s hs) t (hdomain s hs t ht)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-a) a) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · intro t ht
      change t • v ∈ Metric.ball 0 R
      simpa only [zero_smul, add_zero] using hdomain 0 h0 t ht
  have hJ : ∀ t ∈ Ioo (-a) a, ContDiffAt ℝ ∞ (chartField γ (γ t) J) t := by
    intro t ht
    apply radialVariation_contDiffAt_chartField Metric.isOpen_ball he v w
    simpa only [zero_smul, add_zero] using hdomain 0 h0 t ht
  have hjac : ∀ t ∈ Ioo (-a) a,
      manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t =
        -D.curvature (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
    intro t ht
    have hj := manifoldVariation_jacobi g D hS isOpen_Ioo h0 hsmooth hvariation ht
    dsimp only at hj
    rw [show v + (0 : ℝ) • w = v by simp] at hj
    exact eq_neg_of_add_eq_zero_left hj
  have hJ0 : J 0 = 0 := radialVariation_field_zero e v w
  obtain ⟨P, hP0, hPi, hP, hpair, hbound⟩ :=
    ManifoldJacobi.manifold_jacobi_estimates D (by norm_num : (0 : ℝ) < 1)
      isOpen_Ioo hγ hJ hsub hjac hK hc hJ0
  have hh := (hbound 1 ⟨by norm_num, le_rfl⟩).2 (by simpa using hsmall)
  have hR : 0 < R := (norm_nonneg v).trans_lt (by simpa using hv)
  have hinit := g.radialVariation_initial_tangentNorm
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))) hnorm v w
  have hend := radialVariation_field_one v w
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp))
  change g.tangentNorm (γ 0) (manifoldCovDerivAlong g γ J 1 0) = ‖w‖ at hinit
  change J 1 = mfderiv (𝓡 n) (𝓡 n) e v w at hend
  rw [hinit, hend] at hh
  change 1 * ‖w‖ / 2 ≤ g.tangentNorm (e ((1 : ℝ) • v))
    (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
    g.tangentNorm (e ((1 : ℝ) • v)) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤
      3 * 1 * ‖w‖ / 2 at hh
  rw [one_smul, mul_one, one_mul] at hh
  exact hh



theorem exists_uniform_radial_comparison_radius {R : ℝ} (hR : 0 < R) (K : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ ∀ s : ℝ, |s| ≤ 2 * ρ →
      (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) ≤ 3 := by
  have hf : ContinuousAt (fun s : ℝ => (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2))) 0 := by
    fun_prop
  have hnear := hf.eventually_lt continuousAt_const (by norm_num :
    (K * (0 : ℝ) ^ 2) * Real.exp (max 1 (K * (0 : ℝ) ^ 2)) < 3)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min (R / 4) (δ / 4), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · have hh := min_le_left (R / 4) (δ / 4)
    linarith
  · intro s hs
    apply (hsmall (y := s) ?_).le
    rw [Real.dist_eq, sub_zero]
    have hh := min_le_right (R / 4) (δ / 4)
    linarith



theorem pullbackCoefficients_bounds_of_differential
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    (v : EuclideanSpace ℝ (Fin n))
    (hbound : ∀ w, ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
      g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤ 3 * ‖w‖ / 2) :
    ∀ w, (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients e v w w ∧
      g.pullbackCoefficients e v w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2 := by
  intro w
  have hpos : 0 ≤ g.pullbackCoefficients e v w w := by
    change 0 ≤ g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)
      (mfderiv (𝓡 n) (𝓡 n) e v w)
    by_cases hz : mfderiv (𝓡 n) (𝓡 n) e v w = 0
    · rw [hz]
      simp
    · exact (g.pos _ _ hz).le
  have hs : (g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)) ^ 2 =
      g.pullbackCoefficients e v w w := Real.sq_sqrt hpos
  have hh := hbound w
  have hn := norm_nonneg w
  have ht : 0 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) := Real.sqrt_nonneg _
  constructor <;> nlinarith [sq_nonneg (g.tangentNorm (e v)
    (mfderiv (𝓡 n) (𝓡 n) e v w) - ‖w‖ / 2),
    sq_nonneg (g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) + ‖w‖ / 2)]


theorem isInvertible_mfderiv_of_tangentNorm_lower_bound
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    (v : EuclideanSpace ℝ (Fin n))
    (hbound : ∀ w, ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)) :
    (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
  let L := mfderiv (𝓡 n) (𝓡 n) e v
  have hi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro w hw
    have hh := hbound w
    change ‖w‖ / 2 ≤ g.tangentNorm (e v) (L w) at hh
    rw [hw] at hh
    simp only [tangentNorm, map_zero, Real.sqrt_zero] at hh
    exact norm_eq_zero.mp (by linarith [norm_nonneg w])
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) v) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (e v)) := by
    unfold TangentSpace
    infer_instance
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) v) =
      Module.finrank ℝ (TangentSpace (𝓡 n) (e v)) := by
    unfold TangentSpace
    rfl
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  let A := LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩
  exact ⟨A.toContinuousLinearEquiv, rfl⟩



theorem radial_image_mem_ball
    (g : RiemannianMetric n M) {p : M}
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hdist : g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t) :
    e (t • v) ∈ g.ball p R := by
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hR : 0 < R := (norm_nonneg v).trans_lt hvR
  change g.edist p (e (t • v)) < ENNReal.ofReal R
  apply hdist.trans_lt
  have ht1 : ENNReal.ofReal t ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht.2
  calc
    ENNReal.ofReal ‖v‖ * ENNReal.ofReal t ≤ ENNReal.ofReal ‖v‖ * 1 :=
      mul_le_mul_right ht1 _
    _ = ENNReal.ofReal ‖v‖ := mul_one _
    _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR).mpr hvR



theorem radial_exponential_uniform_bounds
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {p : M}
    {e : EuclideanSpace ℝ (Fin n) → M} {R K ρ : ℝ}
    (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) ≤ 3)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ u w, g.pullbackCoefficients e 0 u w = inner ℝ u w)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (e (t • v))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖ ∧
        g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (hK : ∀ x ∈ g.ball p R, D.curvatureTensorNorm x ≤ K) :
    ∀ v ∈ Metric.closedBall 0 (2 * ρ),
      (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible ∧
      ∀ w, (‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
        g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤ 3 * ‖w‖ / 2) ∧
        ((1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients e v w w ∧
          g.pullbackCoefficients e v w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2) := by
  intro v hv
  have hvn : ‖v‖ ≤ 2 * ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hvR : v ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hvn.trans_lt hρR
  have hd : ∀ w, ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
      g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤ 3 * ‖w‖ / 2 := by
    apply g.radial_geodesic_differential_two_sided D he hnorm (fun u hu => (hgeo u hu).1) hvR
    · intro t ht
      exact hK _ (g.radial_image_mem_ball hvR ht ((hgeo v hvR).2 t ht).2)
    · exact fun t ht => ((hgeo v hvR).2 t ht).1
    · exact hsmall ‖v‖ (by simpa only [abs_of_nonneg (norm_nonneg v)] using hvn)
  exact ⟨g.isInvertible_mfderiv_of_tangentNorm_lower_bound v (fun w => (hd w).1),
    fun w => ⟨hd w, g.pullbackCoefficients_bounds_of_differential v hd w⟩⟩

end PoincareConjecture.RiemannianMetric
