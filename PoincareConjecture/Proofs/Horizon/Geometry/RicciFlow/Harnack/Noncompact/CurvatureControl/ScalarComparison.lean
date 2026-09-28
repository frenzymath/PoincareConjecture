import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.LowerSupportComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarContactFinite
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.FiniteContinuity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Bounds









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.RicciFlow



theorem distance_cutoff_mul_scalarCurvature_le_exp_of_finite
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hTheory : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a b δ d₀ Q U0 scale A B C : ℝ}
    (hJ : Icc a b ⊆ interior J) (hm : 0 < m)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M,
      ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ (F.connection t).ricci x v v)
    (p : M) (hδ : 0 < δ) (hd₀ : 0 ≤ d₀) (hQ₀ : 0 < Q)
    (hU0 : 0 ≤ U0) (hscale : 0 < scale)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    (hχrange : ∀ z, χ z ∈ Icc (0 : ℝ) 1)
    (hflat : ∀ z, z ≤ 1 → χ z = 1)
    (hzero : ∀ z, 2 ≤ z → χ z = 0)
    (hA₀ : 0 ≤ A) (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hA : ∀ z, deriv χ z ^ 2 ≤ A * χ z)
    (hB : ∀ z, -B ≤ deriv (deriv χ) z)
    (hC : ∀ z, -C ≤ deriv χ z)
    (hQ : ∀ t ∈ Icc a b, ∀ x ∈ (F.metric t).ball p (d₀ + 2 * δ),
      (F.connection t).scalarCurvature x ≤ Q)
    (hinit : ∀ x ∈ (F.metric a).ball p (d₀ + 2 * δ),
      (F.connection a).scalarCurvature x ≤ U0) :
    let Aheat := C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Q / scale) / δ +
      (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2
    ∀ t ∈ Icc a b, ∀ x : M, (F.metric t).edist p x ≠ ⊤ →
      χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
          (F.connection t).scalarCurvature x ≤
        Real.exp (2 * Q * (t - a)) * (U0 + Aheat / 2) - Aheat / 2 := by
  let H := C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Q / scale) / δ +
    (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2
  change ∀ t ∈ Icc a b, ∀ x : M, (F.metric t).edist p x ≠ ⊤ →
    _ ≤ Real.exp (2 * Q * (t - a)) * (U0 + H / 2) - H / 2
  intro t ht x hxfinite
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hb : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let r := d₀ + 2 * δ
  have hr : 0 < r := by dsimp only [r]; positivity
  let K : Set M := {y | (F.metric b).edist p y ≤ ENNReal.ofReal r}
  let f : M → ℝ → ℝ := fun y s =>
    χ ((((F.metric s).edist p y).toReal - d₀) / δ) * (F.connection s).scalarCurvature y
  have hR (s : ℝ) (hs : s ∈ Icc a b) (y : M) :
      0 ≤ (F.connection s).scalarCurvature y :=
    Finset.sum_nonneg (fun _ _ => hRic s hs y _)
  have hmem (s : ℝ) (y : M)
      (hyfinite : (F.metric s).edist p y ≠ ⊤)
      (hne : χ ((((F.metric s).edist p y).toReal - d₀) / δ) ≠ 0) :
      y ∈ (F.metric s).ball p r := by
    have harg : (((F.metric s).edist p y).toReal - d₀) / δ < 2 :=
      lt_of_not_ge (fun hh => hne (hzero _ hh))
    have hdist : ((F.metric s).edist p y).toReal < r := by
      have hh := (div_lt_iff₀ hδ).mp harg
      dsimp only [r]
      linarith
    change (F.metric s).edist p y < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal hyfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hdist
  have hinto (s : ℝ) (hs : s ∈ Icc a b) :
      (F.metric s).ball p r ⊆ (F.metric b).ball p r :=
    F.ball_subset_ball_of_ricci_nonneg hJ p r hs hb hs.2
      (fun τ hτ y _ v => hRic τ hτ y v)
  have hballK : (F.metric b).ball p r ⊆ K := fun y hy =>
    (show (F.metric b).edist p y < ENNReal.ofReal r from hy).le
  have hcompact : IsCompact K :=
    (F.metric b).isCompact_closedBall_of_metricComplete (hcomplete b hb) p r
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  have hfiniteOn (s : ℝ) (hs : s ∈ Icc a b) (y : M) (hy : y ∈ K) :
      (F.metric s).edist p y ≠ ⊤ :=
    F.edist_ne_top_of_terminal_of_ricci_nonneg hTheory ha.2 hJ (hcomplete b hb)
      hRic p y (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy) hs
  have hdistcont := F.continuousOn_toReal_edist_on_terminal_closedBall_of_ricci_nonneg
    hTheory ha.2 hJ (hcomplete b hb) hRic p hr
  have hscalarcont : ContinuousOn
      (fun z : ℝ × M => (F.connection z.1).scalarCurvature z.2) (Icc a b ×ˢ univ) :=
    (hTheory.scalar_regular (m + 1) M J F).continuousOn.mono
      (fun z hz => ⟨interior_subset (hJ hz.1), trivial⟩)
  have hfcont : ContinuousOn (fun z : ℝ × M => f z.2 z.1) (Icc a b ×ˢ K) :=
    (hχ.continuous.comp_continuousOn
      ((hdistcont.sub continuousOn_const).div_const δ)).mul
        (hscalarcont.mono (Set.prod_mono Subset.rfl (subset_univ K)))
  have hrestricted : ContinuousOn (fun z : K × ℝ => f z.1 z.2) (univ ×ˢ Icc a b) :=
    hfcont.comp
      ((continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).continuousOn)
      (fun z hz => ⟨hz.2, z.1.property⟩)
  have hinitK (y : K) : f y a ≤ U0 := by
    by_cases hz : χ ((((F.metric a).edist p y).toReal - d₀) / δ) = 0
    · simpa only [f, hz, zero_mul] using hU0
    · exact (mul_le_of_le_one_left (hR a ha y) (hχrange _).2).trans
        (hinit y (hmem a y (hfiniteOn a ha y y.property) hz))
  have hcompare := Poincare.Parabolic.le_exp_of_lower_support_deriv_le
    (u := fun y : K => f y) (K := 2 * Q) (B := Q * H) (by positivity)
    (mul_nonneg hQ₀.le hH) hU0 hrestricted hinitK (by
      intro rate q s _ hs hpos hmax
      have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2⟩
      have hqball : (q : M) ∈ (F.metric s).ball p r :=
        hmem s q (hfiniteOn s hs' q q.property) (by
        intro hz
        simp only [f, hz, zero_mul, lt_self_iff_false] at hpos)
      have hqterminal := hinto s hs' hqball
      have hopen : IsOpen ((F.metric b).ball p r) := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
          ⟨(F.metric b).toRiemannianMetric⟩
        let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m + 1)))
            (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
          ⟨⟨(F.metric b).inner, (F.metric b).toContinuousRiemannianMetric.continuous,
            fun _ _ _ => rfl⟩⟩
        let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
        change IsOpen {y : M | edist p y < ENNReal.ofReal r}
        exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
      have hnear : ∀ᶠ y in 𝓝 (q : M), y ∈ (F.metric b).ball p r :=
        hopen.mem_nhds hqterminal
      have hlocal : IsLocalMax (fun y => f y s) (q : M) := by
        filter_upwards [hnear] with y hyball
        have hweighted := hmax (a := (⟨y, hballK hyball⟩, s)) ⟨trivial, hs'⟩
        have hunweighted := (mul_le_mul_iff_right₀
          (Real.exp_pos (-rate * (s - a)))).mp hweighted
        linarith
      have hupper : ∀ y ∈ (F.metric s).ball p r,
          ∀ v : TangentSpace (𝓡 (m + 1)) y,
          (F.connection s).ricci y v v ≤ Q * (F.metric s).inner y v v := by
        intro y hy v
        exact ((F.connection s).ricci_le_scalarCurvature_mul_inner_of_nonneg
          y (hRic s hs' y) v).trans
          (mul_le_mul_of_nonneg_right (hQ s hs' y hy) (by
            by_cases hv : v = 0
            · simp only [hv, map_zero]
              exact le_rfl
            · exact ((F.metric s).pos y v hv).le))
      exact F.exists_lower_time_support_distance_cutoff_scalarCurvature_all_points_of_finite
        hTheory (hJ hs') hm (hcomplete s hs') (hRic s hs') hQ₀.le hscale p q
        hqball hupper (fun τ hτ v => hRic τ ⟨hτ.1, hτ.2.trans hs.2⟩ q v)
        hχ hanti (fun z => (hχrange z).1) hδ hflat hd₀ hA₀ hB₀ hC₀ hA hB hC
        (hQ s hs' q hqball) hpos hlocal)
  have hdivide : Q * H / (2 * Q) = H / 2 := by field_simp
  by_cases hx : x ∈ K
  · simpa only [hdivide] using hcompare ⟨x, hx⟩ t ht
  · have hzeroAt : χ ((((F.metric t).edist p x).toReal - d₀) / δ) = 0 := by
      by_contra hne
      exact hx (hballK (hinto t ht (hmem t x hxfinite hne)))
    rw [hzeroAt, zero_mul]
    have hexp : 1 ≤ Real.exp (2 * Q * (t - a)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) (sub_nonneg.mpr ht.1))
    nlinarith [mul_nonneg (sub_nonneg.mpr hexp) (show 0 ≤ U0 + H / 2 by positivity)]



theorem distance_cutoff_mul_scalarCurvature_le_exp
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hTheory : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a b δ d₀ Q U0 scale A B C : ℝ}
    (hJ : Icc a b ⊆ interior J) (hm : 0 < m)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M,
      ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ (F.connection t).ricci x v v)
    (p : M) (hδ : 0 < δ) (hd₀ : 0 ≤ d₀) (hQ₀ : 0 < Q)
    (hU0 : 0 ≤ U0) (hscale : 0 < scale)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    (hχrange : ∀ z, χ z ∈ Icc (0 : ℝ) 1)
    (hflat : ∀ z, z ≤ 1 → χ z = 1)
    (hzero : ∀ z, 2 ≤ z → χ z = 0)
    (hA₀ : 0 ≤ A) (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hA : ∀ z, deriv χ z ^ 2 ≤ A * χ z)
    (hB : ∀ z, -B ≤ deriv (deriv χ) z)
    (hC : ∀ z, -C ≤ deriv χ z)
    (hQ : ∀ t ∈ Icc a b, ∀ x ∈ (F.metric t).ball p (d₀ + 2 * δ),
      (F.connection t).scalarCurvature x ≤ Q)
    (hinit : ∀ x ∈ (F.metric a).ball p (d₀ + 2 * δ),
      (F.connection a).scalarCurvature x ≤ U0) :
    let Aheat := C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Q / scale) / δ +
      (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2
    ∀ t ∈ Icc a b, ∀ x : M,
      χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
          (F.connection t).scalarCurvature x ≤
        Real.exp (2 * Q * (t - a)) * (U0 + Aheat / 2) - Aheat / 2 := by
  dsimp only
  intro t ht x
  exact F.distance_cutoff_mul_scalarCurvature_le_exp_of_finite hTheory hJ hm hcomplete
    hRic p hδ hd₀ hQ₀ hU0 hscale hχ hanti hχrange hflat hzero hA₀ hB₀ hC₀
    hA hB hC hQ hinit t ht x ((F.metric t).edist_ne_top p x)

end PoincareConjecture.RicciFlow
