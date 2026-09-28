import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.NoBranching
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.BrokenSegment














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [T3Space M] [ConnectedSpace M] in
private theorem norm_smul (g : RiemannianMetric n M) (p : M)
    (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm p (a • v) = |a| * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

private theorem minimizing_leg (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p q : M) {r : ℝ} (hr : 0 < r)
    (hd : g.edist p q = ENNReal.ofReal r) :
    ∃ α : ℝ → M, ∃ v : EuclideanSpace ℝ (Fin n),
      g.IsGeodesicOn α (Icc (0 : ℝ) 1) ∧ α 0 = p ∧ α 1 = q ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (α t)) v 0 ∧
      g.tangentNorm p v = r ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (α s) (α t) = ENNReal.ofReal (|s - t| * r) := by
  obtain ⟨ε, hε, α, hα, hα0, hα1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p q
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hv := (hα.hasDerivAt_chart_at h0 p
    (by rw [hα0]; exact mem_extChartAt_source p)).1
  have hvnorm := hα.initial_tangentNorm_eq_of_edist_segment hε hα0 hv hmin
  have hn : g.tangentNorm p (deriv (fun t => extChartAt (𝓡 n) p (α t)) 0) = r := by
    rw [hd] at hvnorm
    exact (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _) hr.le).mp hvnorm
  refine ⟨α, _, (fun t ht => hα t ⟨by linarith [ht.1], by linarith [ht.2]⟩),
    hα0, hα1, hv, hn, ?_⟩
  intro s hs t ht
  rw [hmin s hs t ht, hd, ENNReal.ofReal_mul (abs_nonneg _)]

omit [T3Space M] [ConnectedSpace M] in
private theorem geodesic_of_germ {g : RiemannianMetric n M}
    {α β : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hα : g.IsGeodesicOn α J) (ht : t ∈ J) (heq : β =ᶠ[𝓝 t] α) :
    g.IsGeodesicOn β {t} := by
  intro u hu
  have hut : u = t := hu
  subst u
  obtain ⟨p, q, v, h⟩ := hα t ht
  refine ⟨p, q, v, ?_⟩
  filter_upwards [h, heq] with s hs he
  exact ⟨he.trans hs.1, hs.2⟩



theorem exists_unit_minimizing_geodesic_through
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {p z q : M} {a s : ℝ} (ha : 0 < a) (hs : s ∈ Icc (0 : ℝ) a)
    (hpz : g.edist p z = ENNReal.ofReal s)
    (hzq : g.edist z q = ENNReal.ofReal (a - s))
    (hpq : g.edist p q = ENNReal.ofReal a) :
    ∃ γ : ℝ → M, g.IsGeodesicOn γ (Icc 0 a) ∧
      γ 0 = p ∧ γ s = z ∧ γ a = q ∧
      (∀ t ∈ Icc 0 a,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) ∧
      ∀ u ∈ Icc 0 a, ∀ v ∈ Icc 0 a,
        g.edist (γ u) (γ v) = ENNReal.ofReal |u - v| := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hbasic : ∃ γ : ℝ → M, g.IsGeodesicOn γ (Icc 0 a) ∧
      γ 0 = p ∧ γ a = q ∧
      (∀ t ∈ Icc 0 a,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) ∧
      ∀ u ∈ Icc 0 a, ∀ v ∈ Icc 0 a,
        g.edist (γ u) (γ v) = ENNReal.ofReal |u - v| := by
    obtain ⟨α, w, hα, hα0, hα1, hw, hn, hmin⟩ := minimizing_leg g hc p q ha hpq
    let γ : ℝ → M := fun t => α (a⁻¹ * t)
    have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) a) : a⁻¹ * t ∈ Icc (0 : ℝ) 1 := by
      rw [← div_eq_inv_mul]
      exact ⟨div_nonneg ht.1 ha.le, (div_le_one ha).mpr ht.2⟩
    have hγ : g.IsGeodesicOn γ (Icc 0 a) := fun t ht =>
      hα.comp_mul a⁻¹ t (htime t ht)
    have hγ0 : γ 0 = p := by simp [γ, hα0]
    have hd : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) (a⁻¹ • w) 0 := by
      have hw' : HasDerivAt (fun t => extChartAt (𝓡 n) p (α t)) w (a⁻¹ * 0) := by
        simpa using hw
      simpa only [γ, Function.comp_def, mul_one] using
        hw'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul a⁻¹)
    have hs0 : g.tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) = 1 := by
      rw [← Poincare.VolumeComparison.tangentNorm_coordDeriv_eq g hγ
        (by simp [ha.le]) hγ0 hd, norm_smul, abs_of_pos (inv_pos.mpr ha), hn,
        inv_mul_cancel₀ ha.ne']
    refine ⟨γ, hγ, hγ0, by simp [γ, ha.ne', hα1], ?_, ?_⟩
    · intro t ht
      exact (Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hγ ht
        (by simp [ha.le])).trans hs0
    · intro u hu v hv
      change g.edist (α (a⁻¹ * u)) (α (a⁻¹ * v)) = _
      rw [hmin _ (htime u hu) _ (htime v hv), ← mul_sub, abs_mul,
        abs_of_pos (inv_pos.mpr ha)]
      congr 1
      field_simp
  by_cases hs0 : s = 0
  · have hpz' : p = z := by
      apply edist_eq_zero.mp
      change g.edist p z = 0
      simpa [hs0] using hpz
    obtain ⟨γ, hγ, hγ0, hγa, hspeed, hmin⟩ := hbasic
    exact ⟨γ, hγ, hγ0, by simpa [hs0, hγ0] using hpz', hγa, hspeed, hmin⟩
  by_cases hsa : s = a
  · have hzq' : z = q := by
      apply edist_eq_zero.mp
      change g.edist z q = 0
      simpa [hsa] using hzq
    obtain ⟨γ, hγ, hγ0, hγa, hspeed, hmin⟩ := hbasic
    exact ⟨γ, hγ, hγ0, by simpa [hsa, hγa] using hzq'.symm, hγa, hspeed, hmin⟩
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hslt : s < a := lt_of_le_of_ne hs.2 hsa
  have has : 0 < a - s := sub_pos.mpr hslt
  obtain ⟨α, v, hα, hα0, hα1, hv, hvn, hαmin⟩ := minimizing_leg g hc z p hspos
    (by simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hpz)
  obtain ⟨β, w, hβ, hβ0, hβ1, hw, hwn, hβmin⟩ := minimizing_leg g hc z q has hzq
  have hopposite := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics z
    hα hβ hα0 hβ0 hv hw (hvn ▸ hspos) (hwn ▸ has)
    (fun u hu t ht => by simpa only [hvn] using (hαmin u hu t ht).le)
    (fun u hu t ht => by simpa only [hwn] using (hβmin u hu t ht).le)
    (by simpa only [hα1, hβ1, hvn, hwn, add_sub_cancel] using hpq)
  rw [hvn, hwn] at hopposite
  let left : ℝ → M := fun t => α ((-s⁻¹) * t + 1)
  let right : ℝ → M := fun t => β ((a - s)⁻¹ * t - (a - s)⁻¹ * s)
  have hl0 : left s = z := by simp [left, hspos.ne', hα0]
  have hr0 : right s = z := by simp [right, hβ0]
  have hl : g.IsGeodesicOn left (Icc 0 s) := by
    intro t ht
    apply hα.comp_affine (-s⁻¹) 1 t
    have hdiv : s⁻¹ * t ≤ 1 := by rw [← div_eq_inv_mul]; exact (div_le_one hspos).mpr ht.2
    constructor <;> nlinarith [mul_nonneg (inv_pos.mpr hspos).le ht.1]
  have hr : g.IsGeodesicOn right (Icc s a) := by
    intro t ht
    apply hβ.comp_affine (a - s)⁻¹ (-((a - s)⁻¹ * s)) t
    change (a - s)⁻¹ * t + -((a - s)⁻¹ * s) ∈ Icc (0 : ℝ) 1
    have heq : (a - s)⁻¹ * t + -((a - s)⁻¹ * s) = (t - s) / (a - s) := by ring
    rw [heq]
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) has.le,
      (div_le_one has).mpr (by linarith [ht.2])⟩
  have hld : HasDerivAt (fun t => extChartAt (𝓡 n) z (left t)) ((-s⁻¹) • v) s := by
    have hv' : HasDerivAt (fun t => extChartAt (𝓡 n) z (α t)) v ((-s⁻¹) * s + 1) := by
      simpa [hspos.ne'] using hv
    simpa only [left, Function.comp_def, mul_one, id_eq] using
      hv'.scomp s (((hasDerivAt_id s).const_mul (-s⁻¹)).add_const 1)
  have hrd : HasDerivAt (fun t => extChartAt (𝓡 n) z (right t)) ((a - s)⁻¹ • w) s := by
    have hw' : HasDerivAt (fun t => extChartAt (𝓡 n) z (β t)) w
        ((a - s)⁻¹ * s - (a - s)⁻¹ * s) := by simpa using hw
    simpa only [right, Function.comp_def, mul_one, id_eq] using
      hw'.scomp s (((hasDerivAt_id s).const_mul (a - s)⁻¹).sub_const ((a - s)⁻¹ * s))
  have heq : left =ᶠ[𝓝 s] right := by
    have hl' : g.IsGeodesicOn left {s} := by
      intro t ht
      have ht' : t = s := ht
      subst t
      exact hl s ⟨hspos.le, le_rfl⟩
    have hr' : g.IsGeodesicOn right {s} := by
      intro t ht
      have ht' : t = s := ht
      subst t
      exact hr s ⟨le_rfl, hslt.le⟩
    apply hl'.eq_nhds_of_initial_data hr'
      (by simp : s ∈ ({s} : Set ℝ)) z
      (by rw [hl0]; exact mem_extChartAt_source z) (hl0.trans hr0.symm)
    rw [hld.deriv, hrd.deriv, hopposite, neg_smul]
  let γ : ℝ → M := fun t => if t ≤ s then left t else right t
  have hlocal : ∀ t ∈ Icc 0 a,
      (t ≤ s ∧ γ =ᶠ[𝓝 t] left) ∨ (s ≤ t ∧ γ =ᶠ[𝓝 t] right) := by
    intro t ht
    rcases lt_trichotomy t s with hlt | rfl | hgt
    · left
      refine ⟨hlt.le, ?_⟩
      filter_upwards [eventually_lt_nhds hlt] with u hu
      simp only [γ, if_pos hu.le]
    · left
      refine ⟨le_rfl, ?_⟩
      filter_upwards [heq] with u hu
      dsimp [γ]
      split_ifs <;> simp_all
    · right
      refine ⟨hgt.le, ?_⟩
      filter_upwards [eventually_gt_nhds hgt] with u hu
      simp only [γ, if_neg (not_le.mpr hu)]
  have hγ : g.IsGeodesicOn γ (Icc 0 a) := by
    intro t ht
    rcases hlocal t ht with ⟨hts, he⟩ | ⟨hst, he⟩
    · exact geodesic_of_germ hl ⟨ht.1, hts⟩ he t rfl
    · exact geodesic_of_germ hr ⟨hst, ht.2⟩ he t rfl
  have hγ0 : γ 0 = p := by simp [γ, hspos.le, left, hα1]
  have hγs : γ s = z := by simp [γ, hl0]
  have hγa : γ a = q := by
    simp only [γ, if_neg (not_le.mpr hslt), right]
    rw [← mul_sub, inv_mul_cancel₀ has.ne', hβ1]
  have hγd : HasDerivAt (fun t => extChartAt (𝓡 n) z (γ t)) ((-s⁻¹) • v) s := by
    have he : γ =ᶠ[𝓝 s] left := by
      filter_upwards [heq] with u hu
      dsimp [γ]
      split_ifs <;> simp_all
    exact hld.congr_of_eventuallyEq (he.fun_comp _)
  have hspeed : ∀ t ∈ Icc 0 a,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1 := by
    intro t ht
    rw [Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hγ ht hs,
      ← Poincare.VolumeComparison.tangentNorm_coordDeriv_eq g hγ hs hγs hγd,
      norm_smul, abs_neg, abs_of_pos (inv_pos.mpr hspos), hvn,
      inv_mul_cancel₀ hspos.ne']
  refine ⟨γ, hγ, hγ0, hγs, hγa, hspeed, ?_⟩
  have hupper {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) a) :=
    Poincare.VolumeComparison.edist_le_of_geodesic_speed_Icc g hγ hspeed hu hv
  have hforward : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a, u ≤ v →
      g.edist (γ u) (γ v) = ENNReal.ofReal (v - u) := by
    intro u hu v hv huv
    have hh := Poincare.MetricCurves.edist_eq_of_broken_segment
      (a := p) (b := q) (c := γ u) (A := u) (B := a - u)
      (x := γ u) (y := γ v)
      (s := 0) (t := v - u) (by simp) hu.1 (sub_nonneg.mpr huv)
      (by linarith [hv.2])
    apply (by simpa only [zero_add] using hh)
    · change g.edist p q = _
      simpa only [add_sub_cancel] using hpq
    · change g.edist p (γ u) ≤ _
      simpa only [hγ0, zero_sub, abs_neg, abs_of_nonneg hu.1, mul_one, sub_zero] using
        hupper (u := 0) ⟨le_rfl, ha.le⟩ hu
    · simp
    · change g.edist (γ u) (γ v) ≤ _
      simpa only [mul_one, abs_of_nonpos (sub_nonpos.mpr huv), neg_sub] using hupper hu hv
    · change g.edist (γ v) q ≤ _
      simpa only [hγa, mul_one, abs_of_nonpos (sub_nonpos.mpr hv.2), neg_sub,
        sub_sub_sub_cancel_right] using hupper (v := a) hv ⟨ha.le, le_rfl⟩
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · simpa only [abs_of_nonpos (sub_nonpos.mpr huv), neg_sub] using hforward u hu v hv huv
  · simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm,
      abs_of_nonneg (sub_nonneg.mpr hvu)] using hforward v hv u hu hvu



theorem toponogov_corresponding_side_of_edist_segments
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {α β : ℝ → M} {p : M} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hα0 : α 0 = p) (hβ0 : β 0 = p)
    (hαmin : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a,
      g.edist (α u) (α v) = ENNReal.ofReal |u - v|)
    (hβmin : ∀ u ∈ Icc (0 : ℝ) b, ∀ v ∈ Icc (0 : ℝ) b,
      g.edist (β u) (β v) = ENNReal.ofReal |u - v|) :
    ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
      s ^ 2 + t ^ 2 - 2 * s * t *
        ((a ^ 2 + b ^ 2 - (g.edist (α a) (β b)).toReal ^ 2) / (2 * a * b)) ≤
          (g.edist (α s) (β t)).toReal ^ 2 := by
  intro s hs t ht
  have hαdist (u : ℝ) (hu : u ∈ Icc (0 : ℝ) a) :
      g.edist p (α u) = ENNReal.ofReal u := by
    simpa only [hα0, zero_sub, abs_neg, abs_of_nonneg hu.1] using
      hαmin 0 ⟨le_rfl, ha.le⟩ u hu
  have hβdist (u : ℝ) (hu : u ∈ Icc (0 : ℝ) b) :
      g.edist p (β u) = ENNReal.ofReal u := by
    simpa only [hβ0, zero_sub, abs_neg, abs_of_nonneg hu.1] using
      hβmin 0 ⟨le_rfl, hb.le⟩ u hu
  obtain ⟨γ, hγ, hγ0, hγs, hγa, hγspeed, hγmin⟩ :=
    g.exists_unit_minimizing_geodesic_through hc ha hs (hαdist s hs)
      (by simpa only [abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] using
        hαmin s hs a ⟨ha.le, le_rfl⟩) (hαdist a ⟨ha.le, le_rfl⟩)
  obtain ⟨σ, hσ, hσ0, hσt, hσb, hσspeed, hσmin⟩ :=
    g.exists_unit_minimizing_geodesic_through hc hb ht (hβdist t ht)
      (by simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using
        hβmin t ht b ⟨hb.le, le_rfl⟩) (hβdist b ⟨hb.le, le_rfl⟩)
  simpa only [hγs, hσt, hγa, hσb] using
    (g.toponogov_comparison D hc hsec ha hb hγ hσ hγ0 hσ0
      hγspeed hσspeed hγmin hσmin).2 s hs t ht



theorem toponogov_equal_radius_of_edist_segments
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {α β : ℝ → M} {p : M} {a : ℝ} (ha : 0 < a)
    (hα0 : α 0 = p) (hβ0 : β 0 = p)
    (hαmin : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a,
      g.edist (α u) (α v) = ENNReal.ofReal |u - v|)
    (hβmin : ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) a,
      g.edist (β u) (β v) = ENNReal.ofReal |u - v|) :
    ∀ s ∈ Icc (0 : ℝ) a,
      (s / a) ^ 2 * (g.edist (α a) (β a)).toReal ^ 2 ≤
        (g.edist (α s) (β s)).toReal ^ 2 := by
  intro s hs
  have hh := g.toponogov_corresponding_side_of_edist_segments D hc hsec ha ha
    hα0 hβ0 hαmin hβmin s hs s hs
  calc
    _ = s ^ 2 + s ^ 2 - 2 * s * s *
        ((a ^ 2 + a ^ 2 - (g.edist (α a) (β a)).toReal ^ 2) / (2 * a * a)) := by
      field_simp
      ring
    _ ≤ _ := hh

end PoincareConjecture.RiemannianMetric
