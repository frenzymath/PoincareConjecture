import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.ZeroRatioDecay
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Uniqueness















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Topology Manifold ContDiff Bundle

universe u

namespace Poincare.Analysis.Calculus




theorem eventually_uniform_spatial_jets_of_uniform_values
    {n : ℕ} {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (J : Set T) (f : ℕ → T → EuclideanSpace ℝ (Fin n) → E)
    (g : EuclideanSpace ℝ (Fin n) → E)
    (hsmooth : ∀ i t, t ∈ J → ContDiffOn ℝ ∞ (f i t) U)
    (hpoint : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, ∀ t ∈ J, dist (f i t x) (g x) < ε)
    (hbound : ∀ C, IsCompact C → C ⊆ U → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ i in atTop, ∀ t ∈ J, ∀ x ∈ C, ‖iteratedFDeriv ℝ m (f i t) x‖ ≤ B)
    (m : ℕ) {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsCompact C) (hCU : C ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ t ∈ J, ∀ x ∈ C,
      dist (iteratedFDeriv ℝ m (f i t) x) (iteratedFDeriv ℝ m g x) < ε := by
  classical
  by_contra hnot
  simp only [eventually_atTop] at hnot
  push Not at hnot
  choose σ hσ τ hτ x hx hbad using hnot
  have hσtop : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  have hvalues (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
      Tendsto (fun k => f (σ k) (τ k) y) atTop (𝓝 (g y)) := by
    apply Metric.tendsto_nhds.2
    intro δ hδ
    filter_upwards [hσtop.eventually (hpoint y hy δ hδ)] with k hk
    exact hk (τ k) (hτ k)
  have hbounded : LocallyEventuallyBoundedDerivatives U (fun k => f (σ k) (τ k)) := by
    intro A hA hAU j
    obtain ⟨B, hB⟩ := hbound A hA hAU j
    refine ⟨B, ?_⟩
    filter_upwards [hσtop.eventually hB] with k hk
    exact hk (τ k) (hτ k)
  have hjets := tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth hU hvalues
    (Eventually.of_forall (fun k => hsmooth (σ k) (τ k) (hτ k))) hbounded m hC hCU
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp hjets ε hε).exists
  exact (not_lt_of_ge (hbad k)) (by simpa only [dist_comm] using hk (x k) (hx k))

end Poincare.Analysis.Calculus

namespace PoincareConjecture.RicciFlow



theorem norm_pullbackCoefficients_sub_zero_le_of_curvature_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (F : RicciFlow n M (Iic 0))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {a K b : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hcurv : ∀ s ∈ Icc (-a) 0, (F.connection s).curvatureTensorNorm (e x) ≤ K)
    (hcoeff : ∀ s ∈ Icc (-a) 0, ‖(F.metric s).pullbackCoefficients e x‖ ≤ b)
    {t : ℝ} (ht : t ∈ Icc (-a) 0) :
    ‖(F.metric t).pullbackCoefficients e x - (F.metric 0).pullbackCoefficients e x‖ ≤
      2 * (n : ℝ) ^ 3 * K * b * a := by
  have hderiv (s : ℝ) (hs : s ∈ Icc (-a) 0) :
      HasDerivWithinAt (fun t => (F.metric t).pullbackCoefficients e x)
        (derivWithin (fun t => (F.metric t).pullbackCoefficients e x) (Iic 0) s)
        (Icc (-a) 0) s := by
    have hd := F.differentiableWithinAt_pullbackCoefficients_time hU he hs.2 hx
    have hd' : HasDerivWithinAt (fun t => (F.metric t).pullbackCoefficients e x)
        (derivWithin (fun t => (F.metric t).pullbackCoefficients e x) (Iic 0) s)
        (Iic 0) s := hd.hasDerivWithinAt
    exact hd'.mono (show Icc (-a) 0 ⊆ Iic 0 from fun _ hu => hu.2)
  have hnorm (s : ℝ) (hs : s ∈ Icc (-a) 0) :
      ‖derivWithin (fun t => (F.metric t).pullbackCoefficients e x) (Iic 0) s‖ ≤
        2 * (n : ℝ) ^ 3 * K * b := by
    apply F.norm_derivWithin_pullbackCoefficients_le (uniqueDiffOn_Iic 0) hU he hs.2 hx
      hb hK ?_ (hcurv s hs)
    intro v
    have h := ((F.metric s).pullbackCoefficients e x).le_opNorm₂ v v
    have hle := (le_abs_self ((F.metric s).pullbackCoefficients e x v v)).trans h
    calc
      _ ≤ ‖(F.metric s).pullbackCoefficients e x‖ * ‖v‖ * ‖v‖ := hle
      _ ≤ b * ‖v‖ ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right (hcoeff s hs) (sq_nonneg ‖v‖)]
  have hmean := (convex_Icc (-a) 0).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hnorm (show (0 : ℝ) ∈ Icc (-a) 0 by constructor <;> linarith) ht
  apply hmean.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonpos ht.2]
  linarith [ht.1]






theorem exists_backward_static_metric_jets_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → M)
    (hcenter : ∀ i, 3 / 4 ≤
      (((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).edist p (q i)).toReal)
    {S : ℝ} (hS : 0 < S) (hSsmall : S < 1 / 8)
    (L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ i, (Φ i).source = Metric.ball 0 S)
    (hzeroΦ : ∀ i, Φ i 0 = q i)
    (horth : ∀ i v w, ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).pullbackCoefficients
        (extChartAt (𝓡 n) (q i)).symm
        (extChartAt (𝓡 n) (q i) (q i)) (L₀ i v) (L₀ i w) = inner ℝ v w)
    (hderiv : ∀ i, HasFDerivAt (fun w => extChartAt (𝓡 n) (q i) (Φ i w))
      (L₀ i).toContinuousLinearMap 0)
    (hgeo : ∀ i w, w ∈ Metric.ball 0 S →
      ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).IsGeodesicOn
        (fun t => Φ i (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S})
    (hdist : ∀ i w, w ∈ Metric.ball 0 S →
      ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).edist (q i) (Φ i w) =
        ENNReal.ofReal ‖w‖)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) {R : ℝ} (hR : 0 < R)
    (hterminal : ∀ x ∈ Metric.ball 0 R, Tendsto
      (fun i => ((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).pullbackCoefficients
        (Φ i) x) atTop (𝓝 (g.euclideanCoefficients x))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ ρ < S / 2 ∧ ∀ m : ℕ,
      TendstoUniformlyOn
        (fun i (z : ℝ × EuclideanSpace ℝ (Fin n)) => iteratedFDeriv ℝ m
          (((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric z.1).pullbackCoefficients (Φ i)) z.2)
        (fun z => iteratedFDeriv ℝ m g.euclideanCoefficients z.2) atTop
        (Icc (-1) 0 ×ˢ Metric.closedBall 0 ρ) := by
  let G (i : ℕ) := F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀
  have htime (i : ℕ) (t : ℝ) (ht : t ≤ 0) : t₀ + t / Q i ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ht (hQ i).le)).trans ht₀
  have hcompleteG : ∀ i t, t ≤ 0 → MetricComplete ((G i).metric t) := by
    intro i t ht
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ (htime i t ht)
  have hoperatorG : ∀ i t, t ≤ 0 → ∀ x,
      ((G i).connection t).NonnegativeCurvatureOperator x := by
    intro i t ht x
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ (htime i t ht) x
  have hdecay (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in atTop, ∀ t ≤ 0,
      ∀ x ∈ ((G i).metric 0).ball (q i) (2 * S),
        ((G i).connection t).curvatureTensorNorm x < ε := by
    filter_upwards [F.eventually_ancientRescaleAt_annular_curvature_lt_of_zero_ratio
      hC hcomplete hoperator hK hbound t₀ ht₀ p hzero Q hQ hQzero
      (by norm_num : (0 : ℝ) < 1 / 2) hε] with i hi
    intro t ht x hx
    have hmargin : 1 / 2 + 2 * S ≤ (((G i).metric 0).edist p (q i)).toReal := by
      have hh := hcenter i
      change 3 / 4 ≤ (((G i).metric 0).edist p (q i)).toReal at hh
      linarith
    exact hi t ht x (((G i).metric 0).radial_lower_bound_on_ball p (q i) hmargin x hx).le
  obtain ⟨r, hr, hrS, hspatial⟩ :=
    exists_ancient_exponential_spatial_jet_bounds hC n (by norm_num : (0 : ℝ) < 1) hS
  let r₀ : ℝ := min R r
  have hr₀ : 0 < r₀ := lt_min hR hr
  have hr₀R : r₀ ≤ R := min_le_left _ _
  have hr₀r : r₀ ≤ r := min_le_right _ _
  have hr₀S : r₀ < S := by linarith
  have hsub (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 r₀) :
      x ∈ Metric.closedBall 0 r :=
    (Metric.closedBall_subset_closedBall hr₀r) (Metric.ball_subset_closedBall hx)
  have hsubS : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r₀ ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball hr₀S.le
  have hmaps (i : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 r₀) :
      Φ i x ∈ ((G i).metric 0).ball (q i) (2 * S) := by
    change ((G i).metric 0).edist (q i) (Φ i x) < ENNReal.ofReal (2 * S)
    rw [hdist i x (hsubS hx), ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)]
    have hxnorm : ‖x‖ < r₀ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    linarith
  have he (i : ℕ) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ i) (Metric.ball 0 S) := by
    simpa only [hsource i] using (Φ i).contMDiffOn
  have hjets (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc (-1) 0, ∀ x ∈ Metric.ball 0 r₀,
        ‖iteratedFDeriv ℝ m (((G i).metric t).pullbackCoefficients (Φ i)) x‖ ≤ B := by
    obtain ⟨B, hB, hjet⟩ := hspatial 1 (by norm_num) m
    refine ⟨B, hB, ?_⟩
    filter_upwards [hdecay 1 zero_lt_one] with i hi
    intro t ht x hx
    exact hjet M (G i) (hcompleteG i) (hoperatorG i) (q i)
      (fun s hs y hy => (hi s hs y hy).le) (L₀ i) (Φ i) (hsource i) (hzeroΦ i)
      (horth i) (hderiv i) (hgeo i) (hdist i) t ht x (hsub x hx) m le_rfl
  have hsmooth (i : ℕ) (t : ℝ) (_ht : t ∈ Icc (-1) 0) :
      ContDiffOn ℝ ∞ (((G i).metric t).pullbackCoefficients (Φ i)) (Metric.ball 0 r₀) := by
    intro x hx
    exact (((G i).metric t).contDiffAt_pullbackCoefficients
      ((he i).contMDiffAt (Metric.isOpen_ball.mem_nhds (hsubS hx)))).contDiffWithinAt
  have hpoint (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 r₀)
      (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in atTop, ∀ t ∈ Icc (-1) 0,
      dist (((G i).metric t).pullbackCoefficients (Φ i) x) (g.euclideanCoefficients x) < ε := by
    obtain ⟨B, hB, hcoefficient⟩ := hjets 0
    let c : ℝ := 2 * (n : ℝ) ^ 3 * B
    have hc : 0 ≤ c := by dsimp [c]; positivity
    let δ : ℝ := ε / (2 * (c + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsmall : c * δ < ε / 2 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (c + 1))).mpr
      nlinarith
    have hterm := Metric.tendsto_nhds.mp (hterminal x ((Metric.ball_subset_ball hr₀R) hx))
      (ε / 2) (by positivity)
    filter_upwards [hcoefficient, hdecay δ hδ, hterm] with i hi hiδ hit
    intro t ht
    have hnorm : ∀ s ∈ Icc (-1) 0,
        ‖((G i).metric s).pullbackCoefficients (Φ i) x‖ ≤ B := by
      intro s hs
      simpa only [norm_iteratedFDeriv_zero] using hi s hs x hx
    have hmove := (G i).norm_pullbackCoefficients_sub_zero_le_of_curvature_bound
      Metric.isOpen_ball (he i) (hsubS hx) (by norm_num : (0 : ℝ) ≤ 1) hδ.le hB
      (fun s hs => (hiδ s hs.2 (Φ i x) (hmaps i x hx)).le) hnorm ht
    have hfirst : dist (((G i).metric t).pullbackCoefficients (Φ i) x)
        (((G i).metric 0).pullbackCoefficients (Φ i) x) < ε / 2 := by
      rw [dist_eq_norm]
      apply hmove.trans_lt
      simpa only [c, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using hδsmall
    exact (dist_triangle _ (((G i).metric 0).pullbackCoefficients (Φ i) x) _).trans_lt
      (by linarith)
  refine ⟨r₀ / 2, by positivity, by linarith, by linarith, ?_⟩
  intro m
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  have hall := Poincare.Analysis.Calculus.eventually_uniform_spatial_jets_of_uniform_values
    Metric.isOpen_ball (Icc (-1 : ℝ) 0)
    (fun i t => ((G i).metric t).pullbackCoefficients (Φ i)) g.euclideanCoefficients
    hsmooth hpoint (fun C _ hCsub m => by
      obtain ⟨B, _, hB⟩ := hjets m
      refine ⟨B, ?_⟩
      filter_upwards [hB] with i hi
      exact fun t ht x hx => hi t ht x (hCsub hx))
    m (isCompact_closedBall 0 (r₀ / 2)) (Metric.closedBall_subset_ball (by linarith)) hε
  filter_upwards [hall] with i hi z hz
  simpa only [dist_comm] using hi z.1 hz.1 z.2 hz.2

end PoincareConjecture.RicciFlow
