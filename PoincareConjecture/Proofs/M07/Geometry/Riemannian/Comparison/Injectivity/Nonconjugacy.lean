import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ManifoldComparison
import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.ComparisonRadius











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open ConnectionVariation ConnectionAlongCurve

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem contDiffAt_chartField_radialVariation_of_ball
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (v w : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : t • v ∈ Metric.ball 0 R) :
    let q : ℝ → M := fun s => e (s • v)
    let J : (s : ℝ) → TangentSpace (𝓡 n) (q s) :=
      fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (fun u : ℝ => e (s • (v + u • w))) 0 1
    ContDiffAt ℝ ∞ (chartField q (q t) J) t := by
  let q : ℝ → M := fun s => e (s • v)
  let c := extChartAt (𝓡 n) (q t)
  let f := c ∘ e
  have het := he.contMDiffAt (Metric.isOpen_ball.mem_nhds ht)
  have hf : ContDiffAt ℝ ∞ f (t • v) :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (mem_chart_source _ _)).comp (t • v) het)
  have hsmooth : ContDiffAt ℝ ∞ (fun s : ℝ => s • fderiv ℝ f (s • v) w) t :=
    contDiffAt_id.smul
      (((hf.fderiv_right (by simp)).comp t (by fun_prop)).clm_apply contDiffAt_const)
  have hline : ContinuousAt (fun s : ℝ => s • v) t := by fun_prop
  have hnear := hline.preimage_mem_nhds
    (inter_mem (Metric.isOpen_ball.mem_nhds ht)
      (het.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds
          (mem_extChartAt_source (I := 𝓡 n) _))))
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [hnear] with s hs
  have hes := (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hs.1)).mdifferentiableAt
    (by simp)
  have hd := mfderiv_comp (s • v)
    (mdifferentiableAt_extChartAt (by
      simpa only [c, extChartAt_source, mem_preimage] using hs.2)) hes
  rw [mfderiv_eq_fderiv] at hd
  change mfderiv (𝓡 n) (𝓡 n) c (e (s • v))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (s • (v + u • w))) 0 1) = _
  rw [radialVariation_field_eq v w s hes]
  have hdw := congrArg (fun L => L (s • w)) hd
  change fderiv ℝ f (s • v) (s • w) =
    mfderiv (𝓡 n) (𝓡 n) c (e (s • v))
      (mfderiv (𝓡 n) (𝓡 n) e (s • v) (s • w)) at hdw
  rw [← hdw, map_smul]



theorem exists_radial_variation_rectangle
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



theorem tangentNorm_mfderiv_bounds_of_radial_geodesics
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ u w, g.pullbackCoefficients e 0 u w = inner ℝ u w)
    (hgeo : ∀ u ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • u)) {t : ℝ | t • u ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (hvr : ‖v‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (e (t • v)) ≤ K)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖)
    (w : EuclideanSpace ℝ (Fin n)) :
    ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
      g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤ 3 * ‖w‖ / 2 := by
  let q : ℝ → M := fun t => e (t • v)
  let J : (t : ℝ) → TangentSpace (𝓡 n) (q t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
  obtain ⟨S, a, hS, h0, ha, hvelocity, hdomain⟩ := exists_radial_variation_rectangle hv w
  have htv (t : ℝ) (ht : t ∈ Ioo (-a) a) : t • v ∈ Metric.ball 0 R := by
    simpa only [zero_smul, add_zero] using hdomain 0 h0 t ht
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q (Ioo (-a) a) :=
    he.comp (contMDiffOn_iff_contDiffOn.mpr (by fun_prop)) htv
  have hJ : ∀ t ∈ Ioo (-a) a, ContDiffAt ℝ ∞ (chartField q (q t) J) t :=
    fun t ht => contDiffAt_chartField_radialVariation_of_ball he v w (htv t ht)
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-a) a := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z : ℝ × ℝ => e (z.2 • (v + z.1 • w))) (S ×ˢ Ioo (-a) a) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact fun z hz => hdomain z.1 hz.1 z.2 hz.2
  have hvariation : ∀ s ∈ S,
      g.IsGeodesicOn (fun t : ℝ => e (t • (v + s • w))) (Ioo (-a) a) :=
    fun s hs t ht => hgeo _ (hvelocity s hs) t (hdomain s hs t ht)
  have hjac : ∀ t ∈ Ioo (-a) a,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    intro t ht
    have h := manifoldVariation_jacobi g D hS isOpen_Ioo h0 hsmooth hvariation ht
    dsimp only at h
    rw [show v + (0 : ℝ) • w = v by simp] at h
    exact eq_neg_of_add_eq_zero_left h
  obtain ⟨P, hP0, hPi, hP, hpair, hestimate⟩ :=
    ManifoldJacobi.manifold_jacobi_estimates D (by norm_num : (0 : ℝ) < 1)
      isOpen_Ioo hq hJ hsub hjac hcurv hspeed (radialVariation_field_zero e v w)
  have hsmall := Poincare.ODE.Jacobi.comparisonRadius_smallness hK
    (norm_nonneg v) hvr (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have h := (hestimate 1 (by simp)).2 (by simpa only [mul_one] using hsmall)
  have he0 := he.contMDiffAt (x := 0)
    (Metric.isOpen_ball.mem_nhds (by simpa using hR))
  have hinitial := g.radialVariation_initial_tangentNorm he0 hnorm v w
  have hfinal := radialVariation_field_one v w
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp))
  change J 1 = mfderiv (𝓡 n) (𝓡 n) e v w at hfinal
  change g.tangentNorm (q 0) (manifoldCovDerivAlong g q J 1 0) = ‖w‖ at hinitial
  rw [hinitial, hfinal] at h
  have hvalue := congrArg (fun x : M => g.tangentNorm x
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w))
    (show q 1 = e v by simp [q])
  rw [hvalue] at h
  simpa only [one_mul, mul_one] using h


theorem bijective_mfderiv_of_tangentNorm_lower_bound
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    (v : EuclideanSpace ℝ (Fin n))
    (hlower : ∀ w, ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e v) := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) e v
  have hinj : Function.Injective A := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have h := hlower w
    change A w = 0 at hw
    change ‖w‖ / 2 ≤ g.tangentNorm (e v) (A w) at h
    rw [hw] at h
    simp only [tangentNorm, map_zero, Real.sqrt_zero] at h
    exact norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg _))
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj
  exact ⟨hinj, hsurj⟩




theorem exists_precompact_exponential_with_differential_bounds [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hcurv : ∀ x ∈ g.ball p R, D.curvatureTensorNorm x ≤ K) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    ∃ L : E ≃L[ℝ] E, ∃ e : E → M,
      (∀ v w, g.pullbackCoefficients c.symm (c p) (L v) (L w) = inner ℝ v w) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      HasFDerivAt (fun v => c (e v)) L.toContinuousLinearMap 0 ∧
      (∀ v ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => e (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (e (t • v))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖ ∧
          g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t) ∧
      ∀ v ∈ Metric.ball 0 R, ‖v‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K →
        Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e v) ∧
        ∀ w, ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
          g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤ 3 * ‖w‖ / 2 := by
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p hR hcompact
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))) he0 hed hL
  refine ⟨L, e, hL, he, he0, hed, hgeo, ?_⟩
  intro v hv hvr
  have hcurv' : ∀ t ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (e (t • v)) ≤ K := by
    intro t ht
    apply hcurv
    change g.edist p (e (t • v)) < ENNReal.ofReal R
    have hvR : ‖v‖ < R := by simpa using hv
    have ht1 : ENNReal.ofReal t ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal ht.2
    exact ((hgeo v hv).2 t ht).2.trans_lt
      ((mul_le_of_le_one_right zero_le ht1).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hvR))
  have hbounds := g.tangentNorm_mfderiv_bounds_of_radial_geodesics D hR hK he hnorm
    (fun u hu => (hgeo u hu).1) hv hvr hcurv' (fun t ht => ((hgeo v hv).2 t ht).1)
  exact ⟨g.bijective_mfderiv_of_tangentNorm_lower_bound v (fun w => (hbounds w).1), hbounds⟩

end PoincareConjecture.RiemannianMetric
