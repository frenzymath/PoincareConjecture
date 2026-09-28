import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ExponentialRays











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]

omit [T3Space M] in
theorem line_geodesic_speed (g : RiemannianMetric 1 M)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)}
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0) (t : ℝ) :
    g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 1) γ t 1) = g.tangentNorm p v := by
  have hconst := isOpen_univ.is_const_of_deriv_eq_zero
    (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
    (fun u hu => (hγ.hasDerivAt_tangentNorm_zero hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hγ.hasDerivAt_tangentNorm_zero hu).deriv)
    (mem_univ t) (mem_univ 0)
  exact hconst.trans (by
    simpa only [chartCoefficients_self, tangentNorm] using
      hγ.tangentNorm_initial (mem_univ 0) hp hv)

omit [T3Space M] in
theorem line_geodesic_chart_speed (g : RiemannianMetric 1 M)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {t : ℝ}
    {v : EuclideanSpace ℝ (Fin 1)}
    (hv : HasDerivAt (fun u => extChartAt (𝓡 1) (γ t) (γ u)) v t) :
    g.tangentNorm (γ t) v =
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 1) γ t 1) := by
  have hc := (contMDiffAt_extChartAt' (I := 𝓡 1) (n := ∞)
    (mem_chart_source _ (γ t))).mdifferentiableAt (by simp)
  have heq := congrArg (fun L => L 1)
    (mfderiv_comp t hc ((hγ.contMDiffAt (mem_univ t)).mdifferentiableAt one_ne_zero))
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun u => extChartAt (𝓡 1) (γ t) (γ u)) t = _ at heq
  rw [hv.deriv] at heq
  change v = (mfderiv (𝓡 1) (𝓡 1) (extChartAt (𝓡 1) (γ t)) (γ t))
    (mfderiv (𝓘(ℝ, ℝ)) (𝓡 1) γ t 1) at heq
  have hchart := congrArg (fun L => L (mfderiv (𝓘(ℝ, ℝ)) (𝓡 1) γ t 1))
    (mfderiv_extChartAt_self (I := 𝓡 1) (x := γ t))
  exact congrArg (g.tangentNorm (γ t)) (heq.trans hchart)



theorem injective_global_line_geodesic [PreconnectedSpace M] [NoncompactSpace M]
    (g : RiemannianMetric 1 M) (hc : MetricComplete g)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)} (hv0 : v ≠ 0)
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0) :
    Function.Injective γ := by
  have hspeed : 0 < g.tangentNorm p v := Real.sqrt_pos.mpr (g.pos p v hv0)
  have hnorm (t : ℝ) :
      g.tangentNorm (γ t) (deriv (fun u => extChartAt (𝓡 1) (γ t) (γ u)) t) =
        g.tangentNorm p v :=
    (line_geodesic_chart_speed g hγ
      (hγ.hasDerivAt_chart_at (mem_univ t) (γ t) (mem_extChartAt_source _)).1).trans
      (line_geodesic_speed g hγ hp hv t)
  have hne (t : ℝ) : deriv (fun u => extChartAt (𝓡 1) (γ t) (γ u)) t ≠ 0 := by
    intro hz
    have hh := hnorm t
    simp only [hz, tangentNorm, map_zero, Real.sqrt_zero] at hh
    exact hspeed.ne' hh.symm
  intro a b hab
  by_contra hneab
  let va := deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) a
  let vb := deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) b
  have hva := (hγ.hasDerivAt_chart_at (mem_univ a) (γ a) (mem_extChartAt_source _)).1
  have hvb := (hγ.hasDerivAt_chart_at (mem_univ b) (γ a)
    (by rw [hab]; exact mem_extChartAt_source _)).1
  obtain ⟨c, hcv⟩ := exists_smul_eq_of_finrank_eq_one
    (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1)
    (hne a) vb
  have hcabs : |c| = 1 := by
    have hna : g.tangentNorm (γ a) va = g.tangentNorm p v := hnorm a
    have hnb : g.tangentNorm (γ a) vb = g.tangentNorm p v := by
      change Real.sqrt (g.inner (γ a) vb vb) = _
      dsimp only [vb]
      rw [hab]
      exact hnorm b
    rw [← hcv] at hnb
    have hsmul : g.tangentNorm (γ a) (c • va) = |c| * g.tangentNorm (γ a) va := by
      simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
    rw [hsmul, hna] at hnb
    exact mul_right_cancel₀ hspeed.ne' (hnb.trans (one_mul _).symm)
  have hleft : g.IsGeodesicOn (fun t => γ (c * t + a)) univ :=
    fun t _ => hγ.comp_affine c a t (mem_univ _)
  have hright : g.IsGeodesicOn (fun t => γ (t + b)) univ :=
    fun t _ => hγ.comp_add b t (mem_univ _)
  have hdleft : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ (c * t + a)))
      (c • va) 0 := by
    have hd : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ t)) va (c * 0 + a) := by
      simpa only [mul_zero, zero_add] using hva
    simpa only [Function.comp_def, id_eq, mul_one] using!
      hd.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul c).add_const a)
  have hdright : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ (t + b))) vb 0 := by
    have hd : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ t)) vb (0 + b) := by
      simpa only [zero_add] using hvb
    simpa only [Function.comp_def, id_eq, one_smul] using!
      hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).add_const b)
  have hall (t : ℝ) : γ (c * t + a) = γ (t + b) :=
    (hleft.eq_nhds_on_of_initial_data hright
      (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected (mem_univ 0) (γ a)
      (by simpa only [mul_zero, zero_add] using mem_extChartAt_source (I := 𝓡 1) (γ a))
      (by simpa only [mul_zero, zero_add] using hab)
      (hdleft.deriv.trans (hcv.trans hdright.deriv.symm)) t (mem_univ t)).self_of_nhds
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hcabs with hc1 | hcm
  · have hperiodic : Function.Periodic γ (b - a) := by
      intro t
      have hh := hall (t - a)
      rw [hc1, one_mul] at hh
      convert hh.symm using 1 <;> congr 1 <;> ring
    have hcompact := hperiodic.compact_of_continuous (sub_ne_zero.mpr (Ne.symm hneab))
      (contMDiffOn_univ.mp hγ.contMDiffOn).continuous
    rw [Set.range_eq_univ.mpr (g.surjective_global_line_geodesic hc hγ hp hv0 hv)] at hcompact
    exact noncompact_univ M hcompact
  · let t := (a - b) / 2
    let s := (a + b) / 2
    have hts : c * t + a = s := by dsimp [t, s]; rw [hcm]; ring
    have hts' : t + b = s := by dsimp [t, s]; ring
    let w := deriv (fun u => extChartAt (𝓡 1) (γ s) (γ u)) s
    have hd := (hγ.hasDerivAt_chart_at (mem_univ s) (γ s) (mem_extChartAt_source _)).1
    have hdL : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ (c * u + a)))
        (c • w) t := by
      have hd' : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ u)) w (c * t + a) := by
        simpa only [hts] using hd
      simpa only [Function.comp_def, id_eq, mul_one] using!
        hd'.scomp t (((hasDerivAt_id t).const_mul c).add_const a)
    have hdR : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ (u + b))) w t := by
      have hd' : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ u)) w (t + b) := by
        simpa only [hts'] using hd
      simpa only [Function.comp_def, id_eq, one_smul] using!
        hd'.scomp t ((hasDerivAt_id t).add_const b)
    have hzero : c • w = w := hdL.unique
      (hdR.congr_of_eventuallyEq (Eventually.of_forall (fun u => congrArg _ (hall u))))
    rw [hcm, neg_one_smul] at hzero
    have hzero' : w + w = 0 := by
      calc
        w + w = (-w) + w := by rw [hzero]
        _ = 0 := neg_add_cancel w
    have htwo : (2 : ℝ) • w = 0 := by simpa only [two_smul] using hzero'
    exact hne s ((smul_eq_zero.mp htwo).resolve_left (by norm_num))



theorem exists_smooth_bijective_line_geodesic [PreconnectedSpace M] [NoncompactSpace M]
    (g : RiemannianMetric 1 M) (hc : MetricComplete g)
    (p : M) (v : EuclideanSpace ℝ (Fin 1)) (hv : v ≠ 0) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ ∧
      Function.Bijective γ ∧ g.IsGeodesicOn γ univ ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0 := by
  obtain ⟨γ, hγ, hp, hd⟩ := g.exists_global_line_geodesic hc p v
  exact ⟨γ, contMDiff_global_line_geodesic hγ,
    ⟨g.injective_global_line_geodesic hc hγ hp hv hd,
      g.surjective_global_line_geodesic hc hγ hp hv hd⟩, hγ, hp, hd⟩

end PoincareConjecture.RiemannianMetric
