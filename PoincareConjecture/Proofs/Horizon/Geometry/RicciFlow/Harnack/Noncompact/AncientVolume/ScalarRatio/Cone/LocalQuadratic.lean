import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.LocalBounds
import Mathlib.Analysis.Calculus.MeanValue














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio



theorem eq_quadratic_of_locally_quadratic
    {F : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J) (hconn : IsPreconnected J)
    {C : ℝ} (hlocal : ∀ t ∈ J, ∃ a b : ℝ,
      F =ᶠ[𝓝 t] fun u => a + b * u + C * u ^ 2 / 2)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ∀ t ∈ J, F t = F t₀ + deriv F t₀ * (t - t₀) + C * (t - t₀) ^ 2 / 2 := by
  have hd (t : ℝ) (ht : t ∈ J) :
      DifferentiableAt ℝ F t ∧ HasDerivAt (deriv F) C t := by
    obtain ⟨a, b, heq⟩ := hlocal t ht
    have hpoly (u : ℝ) : HasDerivAt (fun v : ℝ => a + b * v + C * v ^ 2 / 2)
        (b + C * u) u := by
      convert! (((hasDerivAt_const u a).add
        ((hasDerivAt_id u).const_mul b)).add
        (((hasDerivAt_id u).pow 2).const_mul C |>.div_const 2)) using 1
      simp only [id_eq]
      ring
    have hder : deriv F =ᶠ[𝓝 t] fun u => b + C * u := by
      filter_upwards [heq.eventuallyEq_nhds] with u hu
      exact hu.deriv_eq.trans (hpoly u).deriv
    refine ⟨((hpoly t).congr_of_eventuallyEq heq).differentiableAt, ?_⟩
    simpa only [mul_one] using
      (((hasDerivAt_id t).const_mul C).const_add b).congr_of_eventuallyEq hder
  let b := deriv F t₀ - C * t₀
  have hder (t : ℝ) (ht : t ∈ J) : deriv F t = b + C * t := by
    apply hJ.eqOn_of_deriv_eq hconn
      (fun u hu => (hd u hu).2.differentiableAt.differentiableWithinAt)
      (fun u _ => (((hasDerivAt_id u).const_mul C).const_add b).differentiableAt.differentiableWithinAt)
      (fun u hu => (hd u hu).2.deriv.trans (by
        simpa only [mul_one] using
          (((hasDerivAt_id u).const_mul C).const_add b).deriv.symm))
      ht₀ (by dsimp [b]; ring) ht
  have hpoly (u : ℝ) : HasDerivAt
      (fun t => F t₀ + deriv F t₀ * (t - t₀) + C * (t - t₀) ^ 2 / 2)
      (b + C * u) u := by
    convert! (((hasDerivAt_const u (F t₀)).add
      (((hasDerivAt_id u).sub_const t₀).const_mul (deriv F t₀))).add
      ((((hasDerivAt_id u).sub_const t₀).pow 2).const_mul C |>.div_const 2)) using 1
    dsimp [b]
    ring
  exact hJ.eqOn_of_deriv_eq hconn
    (fun u hu => (hd u hu).1.differentiableWithinAt)
    (fun u _ => (hpoly u).differentiableAt.differentiableWithinAt)
    (fun u hu => (hder u hu).trans (hpoly u).deriv.symm)
    ht₀ (by simp)



theorem interpolation_of_locally_quadratic
    {F : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hI : Icc (0 : ℝ) 1 ⊆ J) {C : ℝ}
    (hlocal : ∀ t ∈ J, ∃ a b : ℝ,
      F =ᶠ[𝓝 t] fun u => a + b * u + C * u ^ 2 / 2) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      F t = (1 - t) * F 0 + t * F 1 - t * (1 - t) * C / 2 := by
  have h := eq_quadratic_of_locally_quadratic hJ hconn hlocal (t₀ := 0) (hI (by simp))
  have h1 := h 1 (hI (by simp))
  intro t ht
  have ht' := h t (hI ht)
  simp only [sub_zero, one_pow, mul_one] at h1 ht'
  rw [ht', h1]
  ring

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem endpoint_injective_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set (E × E)} (hU : IsOpen U) {x : E} (hx : (x, 0) ∈ U)
    {e : E × E → E} (he : ContDiffOn ℝ ∞ e U)
    (hed : HasFDerivAt (fun v => e (x, v)) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ V ∈ 𝓝 (x, (0 : E)), V ⊆ U ∧ InjOn (fun z => (z.1, e z)) V := by
  let A := fderiv ℝ e (x, 0)
  have hea := he.contDiffAt (hU.mem_nhds hx)
  have hA := (hea.differentiableAt (by simp)).hasFDerivAt
  have hright (v : E) : A (0, v) = v := by
    have hd := hA.comp 0 ((hasFDerivAt_const x (0 : E)).prodMk (hasFDerivAt_id (0 : E)))
    exact congrArg (fun L : E →L[ℝ] E => L v) (hd.unique hed)
  have hsplit (u v : E) : A (u, v) = A (u, 0) + v := by
    rw [show (u, v) = (u, 0) + (0, v) by ext <;> simp, map_add, hright]
  let L : (E × E) →L[ℝ] (E × E) := (ContinuousLinearMap.fst ℝ E E).prod A
  have hLi : Function.Injective L := by
    intro a b hab
    change (a.1, A a) = (b.1, A b) at hab
    have hfirst := congrArg Prod.fst hab
    change a.1 = b.1 at hfirst
    have hsecond : A a = A b := congrArg Prod.snd hab
    have hh : A (a.1, 0) + a.2 = A (b.1, 0) + b.2 := by
      simpa only [← hsplit] using hsecond
    rw [hfirst] at hh
    exact Prod.ext hfirst (add_left_cancel hh)
  let L' : (E × E) ≃L[ℝ] (E × E) := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hLi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hLi))
  let H : E × E → E × E := fun z => (z.1, e z)
  have hH := (contDiffOn_fst.prodMk he).contDiffAt (hU.mem_nhds hx)
  have hdH : HasFDerivAt H (L' : (E × E) →L[ℝ] (E × E)) (x, 0) :=
    hasFDerivAt_fst.prodMk hA
  let G := hH.toOpenPartialHomeomorph H hdH (by simp)
  have hxG : (x, 0) ∈ G.source :=
    hH.mem_toOpenPartialHomeomorph_source hdH (by simp)
  exact ⟨G.source ∩ U, inter_mem (G.open_source.mem_nhds hxG) (hU.mem_nhds hx),
    inter_subset_right, G.injOn.mono inter_subset_left⟩



private theorem exists_injective_joint_geodesic_flow
    (g : RiemannianMetric n M) (p : M) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    ∃ (V : Set (E × E)) (Ψ : (E × E) × ℝ → E × E),
      V ∈ 𝓝 (c p, (0 : E)) ∧
      (∀ z ∈ V, Ψ (z, 0) = z) ∧
      (∀ z ∈ V, ∀ t ∈ Ioo (-2 : ℝ) 2,
        (Ψ (z, t)).1 ∈ c.target ∧
        HasDerivAt (fun s => Ψ (z, s)) (coordinateGeodesicField B (Ψ (z, t))) t) ∧
      InjOn (fun z => (z.1, (Ψ (z, 1)).1)) V := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  obtain ⟨W₀, δ, Φ, hW₀, hbase, _, hδ, hΦ, hΦ0, hΦspec⟩ :=
    g.exists_smooth_chart_geodesic_flow p (0 : E)
  let a := δ / 2
  have ha : 0 < a := half_pos hδ
  let S := CoordinateExponential.velocityScale (E := E) a⁻¹
  let W := S ⁻¹' W₀
  let Ψ : (E × E) × ℝ → E × E := fun z =>
    CoordinateExponential.velocityScale a (Φ (S z.1, a * z.2))
  have hW : IsOpen W := hW₀.preimage S.continuous
  have hxW : (c p, (0 : E)) ∈ W := by
    have hz : S (c p, 0) = (c p, 0) := by ext <;> simp [S]
    change S (c p, 0) ∈ W₀
    rw [hz]
    exact hbase
  have htime {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) : a * t ∈ Ioo (-δ) δ := by
    have hl := mul_lt_mul_of_pos_left ht.1 ha
    have hu := mul_lt_mul_of_pos_left ht.2 ha
    dsimp [a] at *
    constructor <;> nlinarith
  have hΨ : ContDiffOn ℝ ∞ Ψ (W ×ˢ Ioo (-2 : ℝ) 2) := by
    apply (CoordinateExponential.velocityScale (E := E) a).contDiff.comp_contDiffOn
    exact hΦ.comp
      ((S.contDiff.comp contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)).contDiffOn
      (fun z hz => ⟨hz.1, htime hz.2⟩)
  have hΨ0 (z : E × E) (hz : z ∈ W) : Ψ (z, 0) = z := by
    dsimp [Ψ]
    rw [mul_zero, hΦ0 (S z) hz]
    ext <;> simp [S, smul_smul, ha.ne']
  have hΨspec (z : E × E) (hz : z ∈ W) (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) :
      (Ψ (z, t)).1 ∈ c.target ∧ HasDerivAt (fun s => Ψ (z, s))
        (coordinateGeodesicField B (Ψ (z, t))) t := by
    exact ⟨(hΦspec (S z) hz (a * t) (htime ht)).1,
      CoordinateExponential.hasDerivAt_velocityScale
        (hΦspec (S z) hz (a * t) (htime ht)).2.1⟩
  let Γ : E → ℝ → M := fun v t => c.symm (Ψ ((c p, v), t)).1
  have hnear : ∀ᶠ v : E in 𝓝 0, (c p, v) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hxW)
  have hgeo : ∀ᶠ v in 𝓝 0, g.IsGeodesicOn (Γ v) (Icc (0 : ℝ) 1) := by
    filter_upwards [hnear] with v hv
    have hh : g.IsGeodesicOn (Γ v) (Ioo (-2 : ℝ) 2) :=
      g.isGeodesicOn_chart_curve p isOpen_Ioo
        (q := fun t => (Ψ ((c p, v), t)).1)
        (w := fun t => (Ψ ((c p, v), t)).2)
        (fun t ht => ⟨(hΨspec _ hv t ht).1,
          (hΨspec _ hv t ht).2.fst, (hΨspec _ hv t ht).2.snd⟩)
    intro t ht
    exact hh t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hinit : ∀ᶠ v in 𝓝 0, Γ v 0 = p := by
    filter_upwards [hnear] with v hv
    dsimp [Γ]
    rw [hΨ0 _ hv]
    exact c.left_inv (mem_extChartAt_source p)
  have hvel : ∀ᶠ v in 𝓝 0,
      HasDerivAt (fun t => c (Γ v t)) v 0 := by
    filter_upwards [hnear] with v hv
    have hd : HasDerivAt (fun t => (Ψ ((c p, v), t)).1) v 0 := by
      have hh : HasDerivAt (fun t => (Ψ ((c p, v), t)).1)
          (Ψ ((c p, v), 0)).2 0 := (hΨspec _ hv 0 (by norm_num)).2.fst
      simpa only [hΨ0 _ hv] using hh
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (-2 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 2)] with t ht
    exact c.right_inv (hΨspec _ hv t ht).1
  obtain ⟨_, hendd⟩ := g.geodesic_endpoint_zero_and_hasFDerivAt p Γ hgeo hinit hvel
  let e : E × E → E := fun z => (Ψ (z, 1)).1
  have he : ContDiffOn ℝ ∞ e W := hΨ.fst.comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, by norm_num⟩)
  have heq : (fun v => e (c p, v)) =ᶠ[𝓝 0] fun v => c (Γ v 1) := by
    filter_upwards [hnear] with v hv
    exact (c.right_inv (hΨspec _ hv 1 (by norm_num)).1).symm
  obtain ⟨V, hV, hVW, hinj⟩ := endpoint_injective_nhds hW hxW he
    (hendd.congr_of_eventuallyEq heq)
  exact ⟨V, Ψ, hV, fun z hz => hΨ0 z (hVW hz),
    fun z hz t ht => hΨspec z (hVW hz) t ht, hinj⟩

private theorem exists_precompact_intrinsic_ball (g : RiemannianMetric n M) (p : M) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (closure (g.ball p R)) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨K, hK, hpK⟩ := exists_compact_mem_nhds p
  obtain ⟨ε, hε, hsub⟩ := EMetric.mem_nhds_iff.mp hpK
  let δ : ℝ≥0∞ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδtop : δ ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right ε 1)
  refine ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' hδtop, ?_⟩
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  apply hsub
  change EDist.edist x p < ε
  rw [edist_comm]
  exact hx.trans_le (by rw [ENNReal.ofReal_toReal hδtop]; exact min_le_left ε 1)

omit [T2Space M] in
private theorem chart_deriv_le_speed
    (g : RiemannianMetric n M) (p : M) {γ : ℝ → M} {J : Set ℝ}
    (hγ : g.IsGeodesicOn γ J) {t : ℝ} (ht : t ∈ J)
    (hs : γ t ∈ (extChartAt (𝓡 n) p).source) {C : ℝ}
    (hC : ∀ w : TangentSpace (𝓡 n) (γ t),
      ‖mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t) w‖ ≤
        C * g.tangentNorm (γ t) w) :
    ‖deriv (fun u => extChartAt (𝓡 n) p (γ u)) t‖ ≤
      C * g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) := by
  have hc := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞)
    (by simpa only [extChartAt_source] using hs)).mdifferentiableAt
    (by simp)
  have heq := congrArg (fun L => L 1)
    (mfderiv_comp t hc ((hγ.contMDiffAt ht).mdifferentiableAt one_ne_zero))
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun u => extChartAt (𝓡 n) p (γ u)) t = _ at heq
  rw [heq]
  exact hC _

private theorem speed_eq_dist_of_minimizing
    {g : RiemannianMetric n M} {γ : ℝ → M} {ε : ℝ}
    (hε : 0 < ε) (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) :
    g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) =
      (g.edist (γ 0) (γ 1)).toReal := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hv := (hγ.hasDerivAt_chart_at h0 (γ 0) (mem_extChartAt_source _)).1
  have hh := hγ.initial_tangentNorm_eq_of_edist_segment hε rfl hv hmin
  have hspeed := hγ.tangentNorm_initial h0 rfl hv
  have hh' := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm (γ 0)
    (deriv (fun u => extChartAt (𝓡 n) (γ 0) (γ u)) 0) from Real.sqrt_nonneg _)] at hh'
  simp only [chartCoefficients_self] at hspeed
  exact hspeed.trans hh'




theorem exists_minimizing_neighborhood_of_small_chart_velocity
    (g : RiemannianMetric n M) (p : M) :
    ∃ U ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧
      ∀ γ : ℝ → M, g.IsGeodesicOn γ (Icc (0 : ℝ) 1) →
        γ 0 ∈ U → γ 1 ∈ U →
        ‖deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0‖ < r →
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1) := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨V, Ψ, hV, hΨ0, hΨ, hinj⟩ := g.exists_injective_joint_geodesic_flow p
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨r₀, C, hr₀, hC, _, _, hbound⟩ := g.exists_compact_coordinate_bounds p
  obtain ⟨R, hR, hcompact⟩ := g.exists_precompact_intrinsic_ball p
  let d := min (R / 8) (r / (8 * C))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdR : d ≤ R / 8 := min_le_left _ _
  have hCd : C * (2 * d) < r := by
    have hsmall := min_le_right (R / 8) (r / (8 * C))
    have hmul := (le_div_iff₀ (by positivity : 0 < 8 * C)).mp hsmall
    change d * (8 * C) ≤ r at hmul
    nlinarith
  let U := g.ball p d ∩ c.source ∩ c ⁻¹' Metric.ball (c p) (min r₀ r)
  have hUnhds : U ∈ 𝓝 p := by
    have hball : g.ball p d ∈ 𝓝 p := by
      have hh := Metric.eball_mem_nhds p (ENNReal.ofReal_pos.mpr hd)
      change {y | EDist.edist p y < ENNReal.ofReal d} ∈ 𝓝 p
      simpa only [Metric.eball, edist_comm] using hh
    exact inter_mem (inter_mem hball ((isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds
      (mem_extChartAt_source p)))
      ((continuousAt_extChartAt (I := 𝓡 n) p).preimage_mem_nhds
        (Metric.ball_mem_nhds _ (lt_min hr₀ hr)))
  have hread (γ : ℝ → M) (hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) 1))
      (hsrc : γ 0 ∈ c.source) (v : E)
      (hv : HasDerivAt (fun t => c (γ t)) v 0) (hz : (c (γ 0), v) ∈ V) :
      c (γ 1) = (Ψ ((c (γ 0), v), 1)).1 := by
    let η : ℝ → M := fun t => c.symm (Ψ ((c (γ 0), v), t)).1
    have hη : g.IsGeodesicOn η (Ioo (-2 : ℝ) 2) :=
      g.isGeodesicOn_chart_curve p isOpen_Ioo
        (q := fun t => (Ψ ((c (γ 0), v), t)).1)
        (w := fun t => (Ψ ((c (γ 0), v), t)).2)
        (fun t ht => ⟨(hΨ _ hz t ht).1,
          (hΨ _ hz t ht).2.fst, (hΨ _ hz t ht).2.snd⟩)
    have hηI : g.IsGeodesicOn η (Icc (0 : ℝ) 1) := fun t ht =>
      hη t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hη0 : η 0 = γ 0 := by
      dsimp [η]
      rw [hΨ0 _ hz]
      exact c.left_inv hsrc
    have hηv : HasDerivAt (fun t => c (η t)) v 0 := by
      have hh : HasDerivAt (fun t => (Ψ ((c (γ 0), v), t)).1) v 0 := by
        have hh₀ : HasDerivAt (fun t => (Ψ ((c (γ 0), v), t)).1)
            (Ψ ((c (γ 0), v), 0)).2 0 := (hΨ _ hz 0 (by norm_num)).2.fst
        simpa only [hΨ0 _ hz] using hh₀
      apply hh.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (by norm_num : (-2 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 2)] with t ht
      exact c.right_inv (hΨ _ hz t ht).1
    have heq := hγ.eq_nhds_of_initial_data hηI (by simp : (0 : ℝ) ∈ Icc 0 1)
      p hsrc hη0.symm (hv.deriv.trans hηv.deriv.symm)
    have hend := hγ.eqOn_of_eq_nhds hηI (convex_Icc (0 : ℝ) 1).isPreconnected
      (by simp) heq (by simp : (1 : ℝ) ∈ Icc 0 1)
    rw [hend]
    exact c.right_inv (hΨ _ hz 1 (by norm_num)).1
  refine ⟨U, hUnhds, r, hr, ?_⟩
  intro γ hγ hx hy hvsmall
  have hxball : g.edist p (γ 0) < ENNReal.ofReal d := hx.1.1
  have hyball : g.edist p (γ 1) < ENNReal.ofReal d := hy.1.1
  have hxy : g.edist (γ 0) (γ 1) < ENNReal.ofReal (2 * d) := by
    have htri := edist_triangle (γ 0) p (γ 1)
    change g.edist (γ 0) (γ 1) ≤ g.edist (γ 0) p + g.edist p (γ 1) at htri
    have hx' : g.edist (γ 0) p < ENNReal.ofReal d := by
      simpa only [edist, Manifold.riemannianEDist_comm] using hxball
    apply htri.trans_lt
    calc
      g.edist (γ 0) p + g.edist p (γ 1) < ENNReal.ofReal d + ENNReal.ofReal d :=
        ENNReal.add_lt_add hx' hyball
      _ = ENNReal.ofReal (2 * d) := by rw [← ENNReal.ofReal_add hd.le hd.le]; congr 1; ring
  have hballcompact : IsCompact (closure (g.ball (γ 0) (R / 2))) := by
    apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro z hz
    have htri := edist_triangle p (γ 0) z
    change g.edist p z ≤ g.edist p (γ 0) + g.edist (γ 0) z at htri
    apply htri.trans_lt
    have hadd := ENNReal.add_lt_add hxball hz
    apply hadd.trans_le
    rw [← ENNReal.ofReal_add hd.le (by positivity : 0 ≤ R / 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hyR : γ 1 ∈ g.ball (γ 0) (R / 2) :=
    hxy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : 2 * d ≤ R / 2))
  obtain ⟨ε, hε, η, hη, hη0, hη1, hηmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball (γ 0) (γ 1)
      (half_pos hR) hballcompact hyR
  have hηmin' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist (η 0) (η 1) := by
    simpa only [hη0, hη1] using hηmin
  have hηspeed := speed_eq_dist_of_minimizing hε hη hηmin'
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hηsrc : η 0 ∈ c.source := hη0 ▸ hx.1.2
  have hxcoord : c (γ 0) ∈ Metric.closedBall (c p) r₀ :=
    (hx.2.trans_le (min_le_left r₀ r)).le
  have hboundη : ∀ w : TangentSpace (𝓡 n) (η 0),
      ‖mfderiv (𝓡 n) (𝓡 n) c (η 0) w‖ ≤ C * g.tangentNorm (η 0) w := by
    have hh := (hbound (c (γ 0)) hxcoord).2
    rw [c.left_inv hx.1.2] at hh
    rw [hη0]
    exact hh
  have hηvsmall : ‖deriv (fun t => c (η t)) 0‖ < r := by
    have hh := g.chart_deriv_le_speed p hη h0 hηsrc hboundη
    rw [hηspeed, hη0, hη1] at hh
    exact (hh.trans_lt (mul_lt_mul_of_pos_left (ENNReal.toReal_lt_of_lt_ofReal hxy) hC)).trans hCd
  have hγv := (hγ.hasDerivAt_chart_at (by simp : (0 : ℝ) ∈ Icc 0 1) p hx.1.2).1
  have hηv := (hη.hasDerivAt_chart_at h0 p hηsrc).1
  have hzγ : (c (γ 0), deriv (fun t => c (γ t)) 0) ∈ V := by
    apply hrV
    rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff]
    exact ⟨hx.2.trans_le (min_le_right r₀ r), hvsmall⟩
  have hzη : (c (η 0), deriv (fun t => c (η t)) 0) ∈ V := by
    apply hrV
    rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff, hη0]
    exact ⟨hx.2.trans_le (min_le_right r₀ r), hηvsmall⟩
  have hηI : g.IsGeodesicOn η (Icc (0 : ℝ) 1) := fun t ht =>
    hη t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hends : (c (γ 0), (Ψ ((c (γ 0), deriv (fun t => c (γ t)) 0), 1)).1) =
      (c (η 0), (Ψ ((c (η 0), deriv (fun t => c (η t)) 0), 1)).1) := by
    rw [← hread γ hγ hx.1.2 _ hγv hzγ, ← hread η hηI hηsrc _ hηv hzη, hη0, hη1]
  have hvel := congrArg Prod.snd (hinj hzγ hzη hends)
  have heq := hγ.eq_nhds_of_initial_data hηI (by simp : (0 : ℝ) ∈ Icc 0 1)
    p hx.1.2 hη0.symm hvel
  have heqI := hγ.eqOn_of_eq_nhds hηI (convex_Icc (0 : ℝ) 1).isPreconnected
    (by simp) heq
  intro s hs t ht
  rw [heqI hs, heqI ht]
  exact hηmin s hs t ht




theorem IsGeodesicOn.exists_minimizing_affine_neighborhood
    {g : RiemannianMetric n M} {γ : ℝ → M} {J : Set ℝ}
    (hγ : g.IsGeodesicOn γ J) (hJ : IsOpen J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ∃ δ : ℝ, 0 < δ ∧ Ioo (t₀ - 3 * δ) (t₀ + 3 * δ) ⊆ J ∧
      let η := fun u => γ (2 * δ * u + (t₀ - δ))
      g.IsGeodesicOn η (Ioo (-1 : ℝ) 2) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist (η 0) (η 1) := by
  let p := γ t₀
  let c := extChartAt (𝓡 n) p
  let q := fun t => c (γ t)
  obtain ⟨U, hU, r, hr, hmin⟩ := g.exists_minimizing_neighborhood_of_small_chart_velocity p
  obtain ⟨a, ha, haJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds ht₀)
  have hc := (hγ.contMDiffAt ht₀).continuousAt
  have hv := (hγ.hasDerivAt_chart_at ht₀ p (mem_extChartAt_source p)).2.continuousAt
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0,
      γ (t₀ - δ) ∈ U ∧ γ (t₀ + δ) ∈ U ∧
      ‖(2 * δ) • deriv q (t₀ - δ)‖ < r ∧ δ < a / 3 ∧ γ (t₀ - δ) ∈ c.source := by
    have hcminus : ContinuousAt (fun δ : ℝ => γ (t₀ - δ)) 0 := by
      exact hc.comp_of_eq (by fun_prop) (by simp)
    have hcplus : ContinuousAt (fun δ : ℝ => γ (t₀ + δ)) 0 := by
      exact hc.comp_of_eq (by fun_prop) (by simp)
    have hvminus : ContinuousAt (fun δ : ℝ => deriv q (t₀ - δ)) 0 := by
      exact hv.comp_of_eq (by fun_prop) (by simp)
    have hvs : ContinuousAt (fun δ : ℝ => ‖(2 * δ) • deriv q (t₀ - δ)‖) 0 :=
      ((show ContinuousAt (fun δ : ℝ => 2 * δ) 0 by fun_prop).smul hvminus).norm
    have hsource : ∀ᶠ δ : ℝ in 𝓝 0, γ (t₀ - δ) ∈ c.source :=
      hcminus.preimage_mem_nhds (by simpa only [sub_zero] using
        (isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds (mem_extChartAt_source p))
    have hUm : ∀ᶠ δ : ℝ in 𝓝 0, γ (t₀ - δ) ∈ U :=
      hcminus.preimage_mem_nhds (by simpa using hU)
    have hUp : ∀ᶠ δ : ℝ in 𝓝 0, γ (t₀ + δ) ∈ U :=
      hcplus.preimage_mem_nhds (by simpa using hU)
    exact hUm.and (hUp.and
        ((hvs.eventually (gt_mem_nhds (by simpa using hr))).and
          ((gt_mem_nhds (by positivity : (0 : ℝ) < a / 3)).and hsource)))
  obtain ⟨b, hb, hbsmall⟩ := Metric.mem_nhds_iff.mp hsmall
  let δ := b / 2
  have hδ : 0 < δ := half_pos hb
  have hδsmall := hbsmall (show δ ∈ Metric.ball (0 : ℝ) b by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ]
    dsimp [δ]
    linarith)
  have hsub : Ioo (t₀ - 3 * δ) (t₀ + 3 * δ) ⊆ J := by
    intro t ht
    apply haJ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hδsmall.2.2.2.1]
  let η := fun u => γ (2 * δ * u + (t₀ - δ))
  have hη : g.IsGeodesicOn η (Ioo (-1 : ℝ) 2) := by
    intro u hu
    apply hγ.comp_affine (2 * δ) (t₀ - δ) u
    apply hsub
    constructor <;> nlinarith [hu.1, hu.2]
  have hηI : g.IsGeodesicOn η (Icc (0 : ℝ) 1) := fun u hu =>
    hη u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hstart : t₀ - δ ∈ J := hsub ⟨by linarith, by linarith⟩
  have hsrc : γ (t₀ - δ) ∈ c.source := hδsmall.2.2.2.2
  have hηv : deriv (fun u => c (η u)) 0 = (2 * δ) • deriv q (t₀ - δ) := by
    have hq := (hγ.hasDerivAt_chart_at hstart p hsrc).1
    have hq' : HasDerivAt q (deriv q (t₀ - δ)) (2 * δ * 0 + (t₀ - δ)) := by
      simpa only [mul_zero, zero_add] using hq
    simpa only [Function.comp_def, id_eq, mul_one] using!
      (hq'.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul (2 * δ)).add_const
        (t₀ - δ))).deriv
  refine ⟨δ, hδ, hsub, hη, hmin η hηI ?_ ?_ ?_⟩
  · simpa only [η, mul_zero, zero_add] using hδsmall.1
  · simpa only [η, mul_one, show 2 * δ + (t₀ - δ) = t₀ + δ by ring] using hδsmall.2.1
  · rw [hηv]
    exact hδsmall.2.2.1

omit [T2Space M] in
private theorem speed_affine {g : RiemannianMetric n M} {γ : ℝ → M}
    {a b : ℝ} (ha : 0 ≤ a)
    (hγ : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ b) :
    g.tangentNorm (γ (a * 0 + b))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t => γ (a * t + b)) 0 1) =
      a * g.tangentNorm (γ b) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ b 1) := by
  have hp : HasDerivAt (fun t : ℝ => a * t + b) a 0 := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id (0 : ℝ)).const_mul a).add_const b
  have hγ' : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ (a * 0 + b) := by
    simpa only [mul_zero, zero_add] using hγ.mdifferentiableAt one_ne_zero
  have hd := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 n) 0
      hγ' hp.differentiableAt.mdifferentiableAt)
  change mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t => γ (a * t + b)) 0 1 =
    mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (a * 0 + b)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun t => a * t + b) 0 1) at hd
  have hp' : fderiv ℝ (fun t : ℝ => a * t + b) 0 1 = a := by
    rw [fderiv_eq_smul_deriv, one_smul, hp.deriv]
  erw [mfderiv_eq_fderiv, hp'] at hd
  have hvel := hd.trans (by simpa only [smul_eq_mul, mul_one] using
    (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (a * 0 + b)).map_smul a (1 : ℝ))
  rw [hvel]
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  exact congrArg (fun t : ℝ =>
    a * g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1))
    (by ring : a * 0 + b = b)




theorem geodesic_quadratic_of_minimizing_geodesic_quadratic
    (g : RiemannianMetric n M) (f : M → ℝ)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2) :
    ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2 := by
  intro γ ε hε hγ
  let J := Ioo (-ε) (1 + ε)
  have hI : Icc (0 : ℝ) 1 ⊆ J := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  rw [hC 0 (hI (by simp))]
  apply Poincare.AncientVolume.ScalarRatio.interpolation_of_locally_quadratic
    isOpen_Ioo (convex_Ioo _ _).isPreconnected hI
  intro t₀ ht₀
  obtain ⟨δ, hδ, hsub, hη, hηmin⟩ :=
    hγ.exists_minimizing_affine_neighborhood isOpen_Ioo ht₀
  let a := 2 * δ
  let b := t₀ - δ
  let η := fun t => γ (a * t + b)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : b ∈ J := hsub ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  have hspeed : g.tangentNorm (η 0)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η 0 1) = a * C :=
    (speed_affine ha.le (hγ.contMDiffAt hb)).trans (congrArg (a * ·) (hC b hb))
  have hformula := hquad η 1 (by norm_num)
    (by simpa only [neg_neg, one_add_one_eq_two] using hη) hηmin
  rw [hspeed] at hformula
  let A := f (η 0)
  let D := f (η 1)
  refine ⟨A - b * (D - A) / a + b * (a + b) * (C : ℝ) ^ 2 / 2,
    (D - A) / a - (a + 2 * b) * (C : ℝ) ^ 2 / 2, ?_⟩
  filter_upwards [Ioo_mem_nhds (by linarith : t₀ - δ < t₀)
    (by linarith : t₀ < t₀ + δ)] with t ht
  have hu : (t - b) / a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · apply div_nonneg _ ha.le
      dsimp [b]
      linarith [ht.1]
    · apply (div_le_one ha).mpr
      dsimp [a, b]
      linarith [ht.2]
  have harg : a * ((t - b) / a) + b = t := by field_simp; ring
  have hh := hformula ((t - b) / a) hu
  change f (γ (a * ((t - b) / a) + b)) =
    (1 - (t - b) / a) * A + (t - b) / a * D -
      (t - b) / a * (1 - (t - b) / a) * (a * C) ^ 2 / 2 at hh
  rw [harg] at hh
  rw [hh]
  field_simp
  ring



theorem geodesic_quadratic_of_minimizing_segments
    (g : RiemannianMetric n M) (f : M → ℝ)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (g.edist (γ 0) (γ 1)).toReal ^ 2 / 2) :
    ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2 := by
  apply g.geodesic_quadratic_of_minimizing_geodesic_quadratic f
  intro γ ε hε hγ hmin t ht
  rw [speed_eq_dist_of_minimizing hε hγ hmin]
  exact hquad γ ε hε hγ hmin t ht




theorem contMDiff_of_locally_lipschitz_minimizing_segments
    (g : RiemannianMetric n M) (f : M → ℝ)
    (hLip : ∀ p : M, ∃ U ∈ 𝓝 (extChartAt (𝓡 n) p p), ∃ C : ℝ≥0,
      LipschitzOnWith C (f ∘ (extChartAt (𝓡 n) p).symm) U)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (g.edist (γ 0) (γ 1)).toReal ^ 2 / 2) :
    ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f :=
  g.contMDiff_of_locally_lipschitz_geodesic_quadratic f hLip
    (g.geodesic_quadratic_of_minimizing_segments f hquad)

end PoincareConjecture.RiemannianMetric
