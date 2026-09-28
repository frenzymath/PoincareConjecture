import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalBall
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Minimizing.ExponentialChord
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.GeodesicLength








noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem isGeodesicOn_and_contMDiffAt_zero_of_edist_affine_segment
    (g : RiemannianMetric n M) {γ : ℝ → M} {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c)
    (hmetric : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
      g.edist (γ s) (γ t) = ENNReal.ofReal (c * |s - t|)) :
    g.IsGeodesicOn γ {0} ∧ ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let p := γ 0
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hγcont : ContinuousAt γ 0 := by
    let C : ℝ≥0 := ⟨c, hc.le⟩
    have hLip : LipschitzOnWith C γ (Ioo (-ε) ε) := by
      intro s hs t ht
      change g.edist (γ s) (γ t) ≤ _
      rw [hmetric s hs t ht, edist_dist, Real.dist_eq,
        ENNReal.ofReal_mul hc.le]
      exact le_of_eq (congrArg (fun a : ℝ≥0∞ => a * ENNReal.ofReal |s - t|)
        (show ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal))
    exact hLip.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hzero)
  obtain ⟨e, h0, he0, he, he', hgauss, _, Γ, _, hΓ⟩ := g.exists_exponential_chart_gauss p
  obtain ⟨r, hr, hsource, hdist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e h0 he0 he he' hgauss
  let T : Set E := {v | g.tangentNorm p v < r}
  have hT : IsOpen T := by
    apply isOpen_lt _ continuous_const
    unfold tangentNorm
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  have h0T : (0 : E) ∈ T := by change g.tangentNorm p 0 < r; simpa [tangentNorm] using hr
  have hUnear : e '' T ∈ 𝓝 p := by
    rw [← he0]
    exact e.image_mem_nhds h0 (hT.mem_nhds h0T)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (isOpen_Ioo.mem_nhds hzero) (hγcont.preimage_mem_nhds hUnear))
  have hsmall (t : ℝ) (ht : |t| < δ) : t ∈ Ioo (-ε) ε ∧ γ t ∈ e '' T :=
    hδsub (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht)
  let v : ℝ → E := fun t => e.symm (γ t)
  have hvT (t : ℝ) (ht : |t| < δ) : v t ∈ T := by
    obtain ⟨w, hw, hew⟩ := (hsmall t ht).2
    change e.symm (γ t) ∈ T
    rw [← hew, e.left_inv (hsource hw)]
    exact hw
  have hev (t : ℝ) (ht : |t| < δ) : e (v t) = γ t := by
    apply e.right_inv
    obtain ⟨w, hw, hew⟩ := (hsmall t ht).2
    exact hew ▸ e.map_source (hsource hw)
  have hvnorm (t : ℝ) (ht : |t| < δ) : g.tangentNorm p (v t) = c * |t| := by
    have h := hdist (v t) (hvT t ht)
    rw [hev t ht] at h
    have hm : g.edist p (γ t) = ENNReal.ofReal (c * |t|) := by
      simpa only [p, zero_sub, abs_neg] using hmetric 0 hzero t (hsmall t ht).1
    exact (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
      (mul_nonneg hc.le (abs_nonneg t))).mp (h.symm.trans hm)
  have hleg (w : E) (hw : w ∈ T) :
      ∃ α : ℝ → M, g.IsGeodesicOn α (Icc (0 : ℝ) 1) ∧
        α 0 = p ∧ α 1 = e w ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (α t)) w 0 ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          g.edist (α s) (α t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p w) := by
    obtain ⟨hinit, hend, hdata⟩ := hΓ w (hsource hw)
    obtain ⟨hα, hα0, hd⟩ := g.geodesic_of_coordinate_exponential p
      (fun t => Γ (w, t)) w hinit hdata
    obtain ⟨C, hC⟩ := hα.exists_constant_tangentNorm (by norm_num : (-2 : ℝ) < 2)
    have hC0 := hC 0 (by norm_num)
    rw [hα.tangentNorm_initial (by norm_num) hα0 hd, chartCoefficients_self] at hC0
    refine ⟨_, (fun t ht => hα t ⟨by linarith [ht.1], by linarith [ht.2]⟩),
      hα0, hend, hd, ?_⟩
    intro s hs t ht
    have hh := hα.edist_le_of_tangentNorm_eq hC
      (show s ∈ Ioo (-2 : ℝ) 2 by constructor <;> linarith [hs.1, hs.2])
      (show t ∈ Ioo (-2 : ℝ) 2 by constructor <;> linarith [ht.1, ht.2])
    rw [← ENNReal.ofReal_coe_nnreal, ← hC0] at hh
    simpa only [ENNReal.ofReal_coe_nnreal, edist_dist, Real.dist_eq,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm, tangentNorm] using hh
  let A : ℝ → E := fun t => (c * |t|)⁻¹ • v t
  have hopposite (s t : ℝ) (hs : |s| < δ) (ht : |t| < δ)
      (hsneg : s < 0) (htpos : 0 < t) : A t = -(A s) := by
    obtain ⟨α, hα, hα0, hα1, hαd, hαupper⟩ := hleg (v s) (hvT s hs)
    obtain ⟨β, hβ, hβ0, hβ1, hβd, hβupper⟩ := hleg (v t) (hvT t ht)
    have hh := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics p
      hα hβ hα0 hβ0 hαd hβd
      (by rw [hvnorm s hs, abs_of_neg hsneg]; exact mul_pos hc (neg_pos.mpr hsneg))
      (by rw [hvnorm t ht, abs_of_pos htpos]; exact mul_pos hc htpos)
      hαupper hβupper (by
        rw [hα1, hβ1, hev s hs, hev t ht, hmetric s (hsmall s hs).1 t (hsmall t ht).1,
          hvnorm s hs, hvnorm t ht]
        congr 1
        rw [abs_of_neg hsneg, abs_of_pos htpos, abs_of_neg (by linarith : s - t < 0)]
        ring)
    simpa only [hvnorm s hs, hvnorm t ht, A] using hh
  let d : ℝ := δ / 2
  have hd : 0 < d := half_pos hδ
  have hdsmall : |d| < δ := by rw [abs_of_pos hd]; dsimp [d]; linarith
  have hndsmall : |-d| < δ := by simpa only [abs_neg] using hdsmall
  let w : E := c • A d
  have hvlinear (t : ℝ) (ht : |t| < δ) : v t = t • w := by
    rcases lt_trichotomy t 0 with hneg | rfl | hpos
    · have hA : A t = -(A d) := by
        have hh := hopposite t d ht hdsmall hneg hd
        exact neg_eq_iff_eq_neg.mp hh.symm
      have hn : c * |t| ≠ 0 := mul_ne_zero hc.ne' (abs_ne_zero.mpr hneg.ne)
      calc
        v t = (c * |t|) • A t := by simp only [A, smul_smul, mul_inv_cancel₀ hn, one_smul]
        _ = t • w := by rw [hA, abs_of_neg hneg]; simp only [w, smul_neg, smul_smul]; module
    · have hv0 : v 0 = 0 := by
        change e.symm p = 0
        rw [← he0, e.left_inv h0]
      simpa only [zero_smul] using hv0
    · have hA : A t = A d :=
        (hopposite (-d) t hndsmall ht (by linarith) hpos).trans
          (hopposite (-d) d hndsmall hdsmall (by linarith) hd).symm
      have hn : c * |t| ≠ 0 := mul_ne_zero hc.ne' (abs_ne_zero.mpr hpos.ne')
      calc
        v t = (c * |t|) • A t := by simp only [A, smul_smul, mul_inv_cancel₀ hn, one_smul]
        _ = t • w := by rw [hA, abs_of_pos hpos]; simp only [w, smul_smul]; congr 1; ring
  have hsame : γ =ᶠ[𝓝 0] fun t => e (t • w) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have ht' : |t| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    rw [← hvlinear t ht']
    exact (hev t ht').symm
  obtain ⟨a, ha, hasource⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds h0)
  have hexp (z : E) (hz : z ∈ Metric.ball 0 a) :
      ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ → M,
        g.IsGeodesicOn η (Ioo (-ε) (1 + ε)) ∧ η 0 = p ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) z 0 ∧ η 1 = e z := by
    obtain ⟨hinit, hend, hdata⟩ := hΓ z (hasource hz)
    obtain ⟨hη, hη0, hd⟩ := g.geodesic_of_coordinate_exponential p
      (fun t => Γ (z, t)) z hinit hdata
    exact ⟨1, zero_lt_one, _, (fun t ht => hη t ⟨by linarith [ht.1], by linarith [ht.2]⟩),
      hη0, hd, hend⟩
  obtain ⟨hinit, _, hdata⟩ := hΓ (v d) (hsource (hvT d hdsmall))
  obtain ⟨hα, hα0, hαd⟩ := g.geodesic_of_coordinate_exponential p
    (fun t => Γ (v d, t)) (v d) hinit hdata
  let α : ℝ → M := fun t => (extChartAt (𝓡 n) p).symm (Γ (v d, t)).1
  have hαsmall : g.IsGeodesicOn α (Ioo (-1 : ℝ) (1 + 1)) :=
    fun t ht => hα t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hscaled (t : ℝ) : (d⁻¹ * t) • v d = t • w := by
    rw [hvlinear d hdsmall, smul_smul]
    congr 1
    field_simp
  have htime : ∀ᶠ t : ℝ in 𝓝 0, d⁻¹ * t ∈ Ioo (-1 : ℝ) (1 + 1) :=
    (by fun_prop : ContinuousAt (fun t : ℝ => d⁻¹ * t) 0).preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (by norm_num))
  have hsmallv : ∀ᶠ t : ℝ in 𝓝 0, t • w ∈ Metric.ball (0 : E) a :=
    (by fun_prop : ContinuousAt (fun t : ℝ => t • w) 0).preimage_mem_nhds
      (by simpa only [zero_smul] using Metric.ball_mem_nhds (0 : E) ha)
  have hagree : γ =ᶠ[𝓝 0] fun t => α (d⁻¹ * t) := by
    filter_upwards [hsame, htime, hsmallv] with t ht htI htv
    rw [ht]
    have hh := g.exponential_eq_geodesic_of_initial_data p
      (ContinuousLinearEquiv.refl ℝ E) e hexp (v := v d) zero_lt_one hαsmall hα0 hαd htI
      (by rw [hscaled]; exact htv)
    change e ((d⁻¹ * t) • v d) = α (d⁻¹ * t) at hh
    rwa [hscaled] at hh
  have hageo : g.IsGeodesicOn (fun t => α (d⁻¹ * t)) {0} := by
    intro t ht
    have ht0 : t = 0 := ht
    subst t
    exact hαsmall.comp_mul d⁻¹ 0 (by norm_num)
  constructor
  · intro t ht
    have ht0 : t = 0 := ht
    subst t
    obtain ⟨q, z, u, hlocal⟩ := hageo 0 rfl
    refine ⟨q, z, u, ?_⟩
    filter_upwards [hlocal, hagree] with t ht heq
    exact ⟨heq.trans ht.1, ht.2⟩
  · have hlin : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun t : ℝ => t • w) 0 := by
      apply contMDiffAt_iff_contDiffAt.mpr
      fun_prop
    have hex : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e ((0 : ℝ) • w) := by
      simpa only [zero_smul] using he.contMDiffAt (e.open_source.mem_nhds h0)
    exact (hex.comp 0 hlin).congr_of_eventuallyEq hsame


theorem contMDiffAt_zero_of_edist_affine_segment
    (g : RiemannianMetric n M) {γ : ℝ → M} {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c)
    (hmetric : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
      g.edist (γ s) (γ t) = ENNReal.ofReal (c * |s - t|)) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ 0 :=
  (g.isGeodesicOn_and_contMDiffAt_zero_of_edist_affine_segment hε hc hmetric).2



theorem isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b c : ℝ} (hc : 0 ≤ c)
    (hmetric : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      g.edist (γ s) (γ t) = ENNReal.ofReal (c * |s - t|)) :
    g.IsGeodesicOn γ (Ioo a b) ∧ ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo a b) := by
  rcases eq_or_lt_of_le hc with hczero | hc
  · subst c
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    have heq (t : ℝ) (ht : t ∈ Ioo a b) : γ =ᶠ[𝓝 t] fun _ => γ t := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      apply edist_eq_zero.mp
      change g.edist (γ s) (γ t) = 0
      simp only [hmetric s hs t ht, zero_mul, ENNReal.ofReal_zero]
    constructor
    · intro t ht
      obtain ⟨p, q, w, h⟩ := g.isGeodesicOn_const (γ t) {t} t rfl
      refine ⟨p, q, w, ?_⟩
      filter_upwards [h, heq t ht] with s hs he
      exact ⟨he.trans hs.1, hs.2⟩
    · intro t ht
      exact (contMDiffAt_const.congr_of_eventuallyEq (heq t ht)).contMDiffWithinAt
  have hpoint (t : ℝ) (ht : t ∈ Ioo a b) :
      g.IsGeodesicOn γ {t} ∧ ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ t := by
    let ε := min (t - a) (b - t)
    have hε : 0 < ε := lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
    have hshift (u : ℝ) (hu : u ∈ Ioo (-ε) ε) : u + t ∈ Ioo a b := by
      have hleft := min_le_left (t - a) (b - t)
      have hright := min_le_right (t - a) (b - t)
      change -min (t - a) (b - t) < u ∧ u < min (t - a) (b - t) at hu
      constructor <;> linarith [hu.1, hu.2]
    obtain ⟨hgeo, hsmooth⟩ := g.isGeodesicOn_and_contMDiffAt_zero_of_edist_affine_segment
      (γ := fun u => γ (u + t)) hε hc (fun u hu v hv => by
        simpa only [add_sub_add_right_eq_sub] using hmetric (u + t) (hshift u hu)
          (v + t) (hshift v hv))
    constructor
    · intro s hs
      have hs' : s = t := hs
      subst s
      have hh := hgeo.comp_affine 1 (-t) t (by simp)
      simpa only [one_mul, add_assoc, neg_add_cancel, add_zero] using hh
    · have hsm : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun u => γ (u + t)) (t - t) := by
        simpa only [sub_self] using hsmooth
      have hsub : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun u : ℝ => u - t) t := by
        apply contMDiffAt_iff_contDiffAt.mpr
        fun_prop
      have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞
          ((fun u => γ (u + t)) ∘ (fun u : ℝ => u - t)) t :=
        ContMDiffAt.comp t hsm hsub
      simpa only [Function.comp_def, sub_add_cancel] using hcomp
  exact ⟨fun t ht => (hpoint t ht).1 t rfl,
    fun t ht => (hpoint t ht).2.contMDiffWithinAt⟩

end PoincareConjecture.RiemannianMetric
