import PoincareConjecture.Proofs.M30.Thm11_8.CanonicalShapeRelatedNeck
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCanonicalShape
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M30

private theorem uniform_time_slice_of_continuousOn
    {Y Z : Type*} [TopologicalSpace Y] [PseudoMetricSpace Z]
    {I : Set ℝ} {K : Set Y} (hK : IsCompact K)
    {f : ℝ × Y → Z} (hf : ContinuousOn f (I ×ˢ K))
    {t : ℝ} (ht : t ∈ I) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝[I] t)) :
    TendstoUniformlyOn (fun k y => f (s k, y)) (fun y => f (t, y)) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  obtain ⟨V, hV, hclose⟩ := hK.mem_uniformity_of_prod
    (f := fun a y => f (a, y)) hf ht (Metric.dist_mem_uniformity hdelta)
  filter_upwards [hs.eventually hV] with k hk
  intro y hy
  simpa only [Set.mem_ofPred_eq, dist_comm] using! hclose (s k) hk y hy

set_option maxHeartbeats 1800000 in

set_option synthInstance.maxHeartbeats 100000 in



theorem related_neck_at_left_endpoint_of_interior_necks
    {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {T epsilon C : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 400)
    (F : RicciFlow 3 M (Icc (-T) 0))
    (hcomplete : MetricComplete (F.metric (-T)))
    (hcanonical : ∀ t ∈ Ioc (-T) 0, ∀ x : M,
      4 < (F.connection t).scalarCurvature x →
      ∃ N : EpsilonNeck (F.metric t),
        N.epsilon = 2 * epsilon ∧ N.connection = F.connection t ∧
        (F.connection t).scalarCurvature x ≤
          4 * max 1 C * (F.connection t).scalarCurvature N.center ∧
        N.carrier ⊆ (F.metric t).ball x
          (4 * max 1 C + (2 * Real.pi + 2 * (2 * epsilon)⁻¹) * max 1 C + 1))
    (x : M) (hx : 4 < (F.connection (-T)).scalarCurvature x) :
    ∃ N : EpsilonNeck (F.metric (-T)),
      N.epsilon = 4 * epsilon ∧ N.connection = F.connection (-T) ∧
      (F.connection (-T)).scalarCurvature x ≤
        16 * max 1 C * (F.connection (-T)).scalarCurvature N.center := by
  classical
  let g := F.metric (-T)
  let D := F.connection (-T)
  let r := D.scalarCurvature x
  let d := max 1 C
  let rho := 4 * d + (2 * Real.pi + 2 * (2 * epsilon)⁻¹) * d + 1
  have hd : 1 ≤ d := le_max_left _ _
  have hdpos : 0 < d := zero_lt_one.trans_le hd
  have hr : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 4) hx
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hleft : -T ∈ Icc (-T) (0 : ℝ) := ⟨le_rfl, by linarith⟩
  let t0 (k : ℕ) := -T + T * (1 / ((k : ℝ) + 1))
  have ht0 (k : ℕ) : t0 k ∈ Ioc (-T) 0 := by
    have hden : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hfrac : 0 < 1 / ((k : ℝ) + 1) := div_pos zero_lt_one hden
    have hfracOne : 1 / ((k : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).mpr (by linarith only [Nat.cast_nonneg (α := ℝ) k])
    constructor <;> dsimp [t0]
    · linarith [mul_pos hT hfrac]
    · linarith [mul_le_mul_of_nonneg_left hfracOne hT.le]
  have ht0lim : Tendsto t0 atTop (𝓝[Icc (-T) 0] (-T)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun k => ⟨(ht0 k).1.le, (ht0 k).2⟩⟩
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := -T)).add
        ((tendsto_const_nhds (x := T)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
  have hscalar0 : TendstoUniformlyOn
      (fun k y => (F.connection (t0 k)).scalarCurvature y)
      D.scalarCurvature atTop ({x} : Set M) :=
    uniform_time_slice_of_continuousOn isCompact_singleton
      (F.contMDiffOn_scalarCurvature.continuousOn.mono
        (Set.prod_mono_right (subset_univ _))) hleft ht0lim
  have hhigh : ∀ᶠ k in atTop,
      4 < (F.connection (t0 k)).scalarCurvature x ∧
        r / 2 ≤ (F.connection (t0 k)).scalarCurvature x := by
    have hh := hscalar0.tendsto_at (mem_singleton x)
    exact (hh.eventually (Ioi_mem_nhds hx)).and
      (hh.eventually (Ici_mem_nhds (by change r / 2 < r; linarith only [hr])))
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hhigh
  let t (k : ℕ) := t0 (k + n0)
  have ht (k : ℕ) : t k ∈ Ioc (-T) 0 := ht0 _
  have htlim : Tendsto t atTop (𝓝[Icc (-T) 0] (-T)) :=
    ht0lim.comp (tendsto_add_atTop_nat n0)
  have htx (k : ℕ) : 4 < (F.connection (t k)).scalarCurvature x ∧
      r / 2 ≤ (F.connection (t k)).scalarCurvature x := hn0 _ (by omega)
  choose N hNeps hNconn hNratio hNball using
    fun k => hcanonical (t k) (ht k) x (htx k).1
  let R := 2 * rho + 1
  have hR : 0 < R := by dsimp [R]; linarith only [hrho]
  have hbuffer : 2 * rho < R := by dsimp [R]; linarith only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let K := closure (g.ball x R)
  have hK : IsCompact K := by
    apply IsCompact.of_isClosed_subset
      (g.isCompact_closedBall_of_metricComplete hcomplete x R) isClosed_closure
    apply closure_minimal
      (fun y (hy : g.edist x y < ENNReal.ofReal R) => hy.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  obtain ⟨centers, radius, hcenters, hcover⟩ :=
    hK.exists_finite_buffered_extChart_ball_cover (𝓡 3) isOpen_univ (subset_univ K)
  let ι := {q : M // q ∈ centers}
  let q : ι → M := Subtype.val
  let c (i : ι) := extChartAt (𝓡 3) (q i)
  let V (i : ι) := ball (c i (q i)) (2 * radius (q i))
  let L (i : ι) := closedBall (c i (q i)) (radius (q i))
  have hrad (i : ι) : 0 < radius (q i) := (hcenters i.val i.property).2.1
  have hV (i : ι) : IsOpen (V i) := isOpen_ball
  have hL (i : ι) : IsCompact (L i) := isCompact_closedBall _ _
  have hLV (i : ι) : L i ⊆ V i := closedBall_subset_ball (by linarith [hrad i])
  have hVtarget (i : ι) : V i ⊆ (c i).target :=
    fun _ hz => ((hcenters i.val i.property).2.2 (ball_subset_closedBall hz)).1
  have hLtarget (i : ι) : L i ⊆ (c i).target := (hLV i).trans (hVtarget i)
  have hcover' : K ⊆ ⋃ i : ι, (c i).symm '' L i := by
    intro y hy
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hcover hy)
    obtain ⟨hzmem, hzy⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨⟨z, hzmem⟩, extChartAt (𝓡 3) z y,
      ball_subset_closedBall hzy.2, (extChartAt (𝓡 3) z).left_inv hzy.1⟩
  let e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞ :=
    (Diffeomorph.refl (𝓡 3) M ∞).toPartialDiffeomorph
  have hjets (i : ι) (m : ℕ) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((F.metric (t k)).pullbackCoefficients (e ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop (L i) := by
    have hcoeff := F.smooth.contDiffOn_spacetime_pullbackCoefficients_within
      (hV i) ((contMDiffOn_extChartAt_symm (q i)).mono (hVtarget i))
    have hcontinuous := M28.continuousOn_spatialJet_of_within
      (uniqueDiffOn_Icc (by linarith : -T < 0)) (hV i) hcoeff m
    exact uniform_time_slice_of_continuousOn (hL i)
      (hcontinuous.mono (Set.prod_mono_right (hLV i))) hleft htlim
  have hscalar : TendstoUniformlyOn
      (fun k y => (F.connection (t k)).scalarCurvature y)
      D.scalarCurvature atTop K :=
    uniform_time_slice_of_continuousOn hK
      (F.contMDiffOn_scalarCurvature.continuousOn.mono
        (Set.prod_mono_right (subset_univ _))) hleft htlim
  have hinverse := eventually_inverse_tangent_bound_of_finite_chart_jets
    g (fun k => F.metric (t k)) (fun _ => e) K (fun _ => subset_univ K)
    q L hL hLtarget hcover' (fun i => hjets i 0)
  have hcapture : ∀ᶠ k in atTop, (N k).carrier ⊆ K := by
    filter_upwards [hinverse] with k hk
    have hh := g.ball_subset_image_ball_of_inverse_tangentNorm_le (F.metric (t k))
      e.toOpenPartialHomeomorph x hR (by norm_num : (0 : ℝ) < 2) hbuffer hK
      (subset_univ K)
      (fun z hz => (e.contMDiffOn_invFun.contMDiffAt
        (e.open_target.mem_nhds hz)).of_le (by simp)) hk
    intro z hz
    have hzball : z ∈ g.ball x (2 * rho) := by
      have hz' := hh (hNball k hz)
      change z ∈ id '' g.ball x (2 * rho) at hz'
      simpa only [image_id] using hz'
    exact subset_closure (hzball.trans_le (ENNReal.ofReal_le_ofReal hbuffer.le))
  have hcontinuous : ContinuousOn D.scalarCurvature K :=
    (F.contMDiff_scalarCurvature (-T) hleft).continuous.continuousOn
  obtain ⟨b, hb⟩ := hK.bddAbove_image hcontinuous
  let a := r / (8 * d)
  have ha : 0 < a := by dsimp [a]; positivity
  have hlower (k : ℕ) : a ≤ (F.connection (t k)).scalarCurvature (N k).center := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * d)).mpr
    have hh := (htx k).2.trans (hNratio k)
    change r / 2 ≤ 4 * d * (F.connection (t k)).scalarCurvature (N k).center at hh
    nlinarith only [hh]
  have hbounds : ∀ᶠ k in atTop, (N k).carrier ⊆ K ∧
      (F.connection (t k)).scalarCurvature (N k).center ≤ b + 1 := by
    filter_upwards [hcapture, Metric.tendstoUniformlyOn_iff.mp hscalar 1 zero_lt_one]
      with k hk hkscalar
    have hz : (N k).center ∈ K :=
      hk ((N k).central_sphere_subset (N k).center_on_central_sphere)
    have hbz := hb (mem_image_of_mem D.scalarCurvature hz)
    have herr := hkscalar (N k).center hz
    rw [Real.dist_eq, abs_sub_lt_iff] at herr
    exact ⟨hk, by linarith only [hbz, herr.1, herr.2]⟩
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp hbounds
  have hcap (k : ℕ) : (N (k + n1)).carrier ⊆ e '' K := by
    change (N (k + n1)).carrier ⊆ id '' K
    simpa only [image_id] using (hn1 (k + n1) (by omega)).1
  have hepseta : 2 * epsilon < 4 * epsilon := by linarith
  have heta : 4 * epsilon < 1 / 2 := by linarith
  have horder : ⌊(4 * epsilon)⁻¹⌋₊ + 1 ≤ ⌊(2 * epsilon)⁻¹⌋₊ := by
    apply Nat.le_floor
    have hinv : 400 ≤ epsilon⁻¹ := by
      have hh := inv_anti₀ hepsilon hepsilonSmall
      norm_num at hh
      exact hh
    have hf : (⌊(4 * epsilon)⁻¹⌋₊ : ℝ) ≤ (4 * epsilon)⁻¹ :=
      Nat.floor_le (by positivity)
    have hfour : (4 * epsilon)⁻¹ = epsilon⁻¹ / 4 := by
      rw [mul_inv_rev, div_eq_mul_inv]
    have htwo : (2 * epsilon)⁻¹ = epsilon⁻¹ / 2 := by
      rw [mul_inv_rev, div_eq_mul_inv]
    rw [hfour] at hf
    rw [hfour, htwo]
    push_cast
    linarith only [hinv, hf]
  have hscalar1 := hscalar.seq_tendstoUniformlyOn
    (fun k => k + n1) (tendsto_add_atTop_nat n1)
  have htransfer := eventually_exists_neck_of_captured_finite_metric_jets
    g D (fun k => F.metric (t (k + n1))) (fun k => F.connection (t (k + n1)))
    (mul_pos (by norm_num) hepsilon) hepseta heta horder univ isOpen_univ
    (fun _ => e) (fun _ => rfl) (fun k => N (k + n1)) (fun k => hNeps (k + n1))
    K hK (subset_univ K) hcap a (b + 1) ha
    (fun k => ⟨hlower (k + n1), (hn1 (k + n1) (by omega)).2⟩)
    hscalar1 q L hL hLtarget (fun _ => subset_univ _) hcover'
    (fun i m _ => (hjets i m).seq_tendstoUniformlyOn
      (fun k => k + n1) (tendsto_add_atTop_nat n1))
  obtain ⟨k, hkneck, hkerror⟩ := (htransfer.and
    (Metric.tendstoUniformlyOn_iff.mp hscalar1 (a / 2) (half_pos ha))).exists
  obtain ⟨Vneck, hVeps, hVcenter, hVconn, _hVmap⟩ := hkneck
  have hz : (N (k + n1)).center ∈ K := (hn1 _ (by omega)).1
    ((N (k + n1)).central_sphere_subset (N (k + n1)).center_on_central_sphere)
  have herr := hkerror (N (k + n1)).center hz
  rw [Real.dist_eq, abs_sub_lt_iff] at herr
  have hlow := hlower (k + n1)
  have hratio := (htx (k + n1)).2.trans (hNratio (k + n1))
  change r / 2 ≤ 4 * d *
    (F.connection (t (k + n1))).scalarCurvature (N (k + n1)).center at hratio
  have hcenter : Vneck.center = (N (k + n1)).center := hVcenter
  refine ⟨Vneck, hVeps, hVconn, ?_⟩
  rw [hcenter]
  change r ≤ 16 * d * D.scalarCurvature (N (k + n1)).center
  have hhalf : (F.connection (t (k + n1))).scalarCurvature (N (k + n1)).center / 2 ≤
      D.scalarCurvature (N (k + n1)).center := by linarith only [hlow, herr.1, herr.2]
  have hh := mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 16 * d by positivity)
  nlinarith only [hratio, hh]

end PoincareConjecture.M30
