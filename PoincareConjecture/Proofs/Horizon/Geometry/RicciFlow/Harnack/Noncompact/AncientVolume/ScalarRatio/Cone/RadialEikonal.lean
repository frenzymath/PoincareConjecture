import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialCalibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.GradientBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]
  {g : RiemannianMetric n M}

omit [T3Space M] [PreconnectedSpace M] in

theorem gradient_norm_le_of_local_distance_lipschitz (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} {W : Set M} (hW : W ∈ 𝓝 x)
    (hLip : ∀ y ∈ W, |f x - f y| ≤ (g.edist x y).toReal)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) :
    g.tangentNorm x (D.gradient f x) ≤ 1 := by
  apply (D.gradient_norm_le_iff f x zero_le_one).mpr
  intro v
  obtain ⟨δ, hδ, _, γ, hγ, hp, hv⟩ := g.exists_geodesic_initial_data x v
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hγd := (hγ.contMDiffOn.contMDiffAt (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  subst x
  have hchart := mdifferentiableAt_extChartAt (I := 𝓡 n) (mem_chart_source _ (γ 0))
  have heq := congrArg (fun L => L 1) (mfderiv_comp 0 hchart hγd)
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun t => extChartAt (𝓡 n) (γ 0) (γ t)) 0 = _ at heq
  rw [hv.deriv, mfderiv_extChartAt_self] at heq
  change v = mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1 at heq
  have hd := (hf.hasMFDerivAt.comp 0 hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun t => f (γ t))
    (mvfderiv (𝓡 n) f (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1)) 0 at hd
  rw [← heq] at hd
  have hnorm := (hγ.tangentNorm_initial h0 rfl hv).symm
  rw [← heq] at hnorm
  simp only [one_mul]
  apply hd.le_of_lip' (C := g.tangentNorm (γ 0) v) (Real.sqrt_nonneg _)
  filter_upwards [isOpen_Ioo.mem_nhds h0, hγd.continuousAt.preimage_mem_nhds hW] with t ht htW
  have hdist := hγ.edist_le_initial_speed h0 rfl hv ht
  rw [hnorm] at hdist
  have hdist' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hdist
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (show 0 ≤ g.tangentNorm (γ 0) v from Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (abs_nonneg _)] at hdist'
  simpa only [Real.norm_eq_abs, sub_zero, abs_sub_comm] using (hLip (γ t) htW).trans hdist'

theorem one_le_gradient_norm_of_local_radial_calibration (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} {W : Set M} (hW : W ∈ 𝓝 x)
    (hf : ∀ y ∈ W, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f y)
    {δ : ℝ} (hδ : 0 < δ)
    (hcal : ∀ r : ℝ, 0 < r → r < δ → ∃ y : M,
      (g.edist x y).toReal = r ∧ f y = f x - r) :
    1 ≤ g.tangentNorm x (D.gradient f x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  by_contra h
  obtain ⟨C, hCgrad, hC1⟩ := exists_between (lt_of_not_ge h)
  have hC0 : 0 < C := (Real.sqrt_nonneg _).trans_lt hCgrad
  let K : ℝ≥0 := ⟨C, hC0.le⟩
  have hxW := mem_of_mem_nhds hW
  have hgrad := D.contMDiffAt_gradient (hf x hxW)
  have hpair := ((g.contMDiff x).clm_bundle_apply hgrad).clm_bundle_apply hgrad
  have hcont : ContinuousAt (fun z => g.tangentNorm z (D.gradient f z)) x := by
    exact (Bundle.contMDiffAt_totalSpace.mp hpair).2.continuousAt.sqrt
  let s : Set M := W ∩ {z | g.tangentNorm z (D.gradient f z) < C}
  have hs : s ∈ 𝓝 x := inter_mem hW (hcont.eventually_lt_const hCgrad)
  have hbound (z : M) (hz : z ∈ s) : ‖mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f z‖ₑ ≤ K := by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    apply ContinuousLinearMap.opNorm_le_bound _ hC0.le
    intro v
    change ‖mvfderiv (𝓡 n) f z v‖ ≤ C * g.tangentNorm z v
    rw [Real.norm_eq_abs]
    exact (D.abs_mvfderiv_le_gradient_norm f z v).trans
      (mul_le_mul_of_nonneg_right hz.2.le (Real.sqrt_nonneg _))
  obtain ⟨V, hV, _, hLip⟩ :=
    Poincare.exists_nhds_edist_le_mul_riemannianEDist_of_mfderiv_le
      (I := 𝓡 n) hs (fun z hz => (hf z hz.1).of_le (by simp))
      (show 0 < K from hC0) hbound
  obtain ⟨r, hr, hrV⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 n) hV
  let a := min (r : ℝ) δ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a < δ := by dsimp [a]; linarith [min_le_right (r : ℝ) δ]
  have har : a < r := by dsimp [a]; linarith [min_le_left (r : ℝ) δ]
  obtain ⟨y, hxy, hfy⟩ := hcal a ha haδ
  have hxy' : g.edist x y = ENNReal.ofReal a := by
    rw [← hxy, ENNReal.ofReal_toReal]
    exact g.edist_ne_top x y
  have hyV : y ∈ V := by
    apply hrV
    change g.edist x y < (r : ℝ≥0∞)
    rw [hxy', ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hr)).mpr har
  have hdist := hLip x (mem_of_mem_nhds hV) y hyV
  change EDist.edist (f x) (f y) ≤ (K : ℝ≥0∞) * g.edist x y at hdist
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (g.edist_ne_top _ _)) hdist
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, hxy, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq, hfy,
    sub_sub_cancel, abs_of_pos ha] at hreal
  change a ≤ C * a at hreal
  nlinarith

theorem gradient_normSq_eq_two_mul_of_radial_calibration (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} {W : Set M} (hW : W ∈ 𝓝 x)
    (hf : ∀ y ∈ W, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f y)
    (hpos : ∀ y ∈ W, 0 < f y)
    (hLip : ∀ y ∈ W,
      |Real.sqrt (2 * f x) - Real.sqrt (2 * f y)| ≤ (g.edist x y).toReal)
    {δ : ℝ} (hδ : 0 < δ) (hδf : δ ≤ Real.sqrt (2 * f x))
    (hcal : ∀ r : ℝ, 0 < r → r < δ → ∃ y : M,
      (g.edist x y).toReal = r ∧ f y = (Real.sqrt (2 * f x) - r) ^ 2 / 2) :
    g.inner x (D.gradient f x) (D.gradient f x) = 2 * f x := by
  let ρ : M → ℝ := fun y => Real.sqrt (2 * f y)
  have hρ (y) (hy : y ∈ W) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ y := by
    exact (Real.contDiffAt_sqrt (ne_of_gt (mul_pos zero_lt_two (hpos y hy)))).contMDiffAt.comp y
      (contMDiffAt_const.mul (hf y hy))
  have hxW := mem_of_mem_nhds hW
  have hle := D.gradient_norm_le_of_local_distance_lipschitz hW hLip
    ((hρ x hxW).mdifferentiableAt (by simp))
  have hge := D.one_le_gradient_norm_of_local_radial_calibration hW hρ hδ
    (fun r hr hrδ => by
      obtain ⟨y, hxy, hfy⟩ := hcal r hr hrδ
      refine ⟨y, hxy, ?_⟩
      dsimp only [ρ]
      rw [hfy, show 2 * ((Real.sqrt (2 * f x) - r) ^ 2 / 2) =
        (Real.sqrt (2 * f x) - r) ^ 2 by ring,
        Real.sqrt_sq (sub_nonneg.mpr (hrδ.le.trans hδf))])
  have hnorm : g.tangentNorm x (D.gradient ρ x) = 1 := le_antisymm hle hge
  have hnormSq : g.inner x (D.gradient ρ x) (D.gradient ρ x) = 1 := by
    have hnonneg : 0 ≤ g.inner x (D.gradient ρ x) (D.gradient ρ x) := by
      by_cases hz : D.gradient ρ x = 0
      · simp [hz]
      · exact (g.pos x _ hz).le
    have hs := Real.sq_sqrt hnonneg
    change Real.sqrt (g.inner x (D.gradient ρ x) (D.gradient ρ x)) = 1 at hnorm
    rw [hnorm, one_pow] at hs
    exact hs.symm
  have hF : HasDerivAt (fun s : ℝ => s ^ 2 / 2) (ρ x) (ρ x) := by
    simpa using ((hasDerivAt_id (ρ x)).pow 2).div_const 2
  have hgrad := D.gradient_comp ((hρ x hxW).mdifferentiableAt (by simp)) hF.differentiableAt
  rw [hF.deriv] at hgrad
  have heq : (fun s : ℝ => s ^ 2 / 2) ∘ ρ =ᶠ[𝓝 x] f := by
    filter_upwards [hW] with y hy
    dsimp [ρ]
    rw [Real.sq_sqrt (mul_nonneg zero_le_two (hpos y hy).le)]
    ring
  have hgradEq : D.gradient ((fun s : ℝ => s ^ 2 / 2) ∘ ρ) x = D.gradient f x := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  rw [hgradEq] at hgrad
  rw [hgrad]
  simp only [map_smul, smul_apply, smul_eq_mul, hnormSq, mul_one]
  change ρ x * ρ x = 2 * f x
  rw [← sq]
  exact Real.sq_sqrt (mul_nonneg zero_le_two (hpos x hxW).le)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

theorem exists_local_radial_eikonal_of_normal_chart_coefficients
    (g : ℕ → RiemannianMetric n M) (hc : ∀ k, MetricComplete (g k))
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData h)
    (p : M) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S : ℝ} (hS : 0 < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (g k).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (g k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V) (hzeroV : 0 ∈ V)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => (g k).pullbackCoefficients (Φ k))
        h.euclideanCoefficients atTop K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfzero : 0 < f 0)
    (hf : ∀ x ∈ V, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hpotential : TendstoUniformlyOn
      (fun k x => ((g k).edist p (Φ k x)).toReal ^ 2 / 2) f atTop V) :
    ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ V ∧
      ∀ x ∈ U, 0 < f x ∧ h.inner x (D.gradient f x) (D.gradient f x) = 2 * f x := by
  obtain ⟨W, hWo, hW0, hWV, _, hdist⟩ :=
    exists_uniform_distance_limit_of_normal_chart_coefficients g h q Φ hS
      hsource htarget hradial hV hzeroV hconv
  have hcont : ContinuousOn f W := fun x hx => (hf x (hWV hx)).continuousAt.continuousWithinAt
  have hposnb : {x : EuclideanSpace ℝ (Fin n) | 0 < f x} ∈ 𝓝 0 :=
    (hf 0 hzeroV).continuousAt.eventually (eventually_gt_nhds hfzero)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hWo.mem_nhds hW0) hposnb)
  let R := min ρ S / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRρ : R < ρ := by dsimp [R]; linarith [min_le_left ρ S]
  have hRS : R < S := by dsimp [R]; linarith [min_le_right ρ S]
  have hRW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ W :=
    fun x hx => (hρsub (Metric.closedBall_subset_ball hRρ hx)).1
  have hpos (x) (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) : 0 < f x :=
    (hρsub (Metric.closedBall_subset_ball hRρ hx)).2
  have hUR : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 4) ⊆ Metric.closedBall 0 R :=
    fun x hx => Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by linarith)) hx)
  have hPair (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W)
      (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ W) : Tendsto
      (fun k => ((g k).edist (Φ k x) (Φ k y)).toReal) atTop (𝓝 ((h.edist x y).toReal)) :=
    hdist.tendsto_at (show (x, y) ∈ W ×ˢ W from ⟨hx, hy⟩)
  have hPot (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) : Tendsto
      (fun k => ((g k).edist p (Φ k x)).toReal ^ 2 / 2) atTop (𝓝 (f x)) :=
    hpotential.tendsto_at (hWV hx)
  have hLip : ∀ x ∈ W, ∀ y ∈ W,
      |Real.sqrt (2 * f x) - Real.sqrt (2 * f y)| ≤ (h.edist x y).toReal :=
    radial_lipschitz_of_distance_and_potential_limits g h p (fun k => Φ k) f hPair hPot
  refine ⟨Metric.ball 0 (R / 4), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    hUR.trans (hRW.trans hWV), ?_⟩
  intro x hx
  have hxR := hUR hx
  refine ⟨hpos x hxR, ?_⟩
  let δ := min (R / 4) (Real.sqrt (2 * f x))
  have hδ : 0 < δ := lt_min (by positivity)
    (Real.sqrt_pos.mpr (mul_pos zero_lt_two (hpos x hxR)))
  apply D.gradient_normSq_eq_two_mul_of_radial_calibration
    (W := Metric.closedBall 0 R) ?_ (fun y hy => hf y (hWV (hRW hy))) hpos
    (fun y hy => hLip x (hRW hxR) y (hRW hy)) hδ (min_le_right _ _) ?_
  · exact mem_of_superset (Metric.isOpen_ball.mem_nhds hx) hUR
  · intro r hr hrδ
    obtain ⟨w, _, hd, hw, _⟩ := exists_radial_calibration_of_normal_chart_limits g hc h p q Φ hRS
      hsource htarget hradial hRW hdist f hcont (hpotential.mono hWV) hx hr
      (hrδ.trans_le (min_le_left _ _)) (hrδ.trans_le (min_le_right _ _))
    exact ⟨w, hd, hw⟩

end PoincareConjecture.RiemannianMetric
