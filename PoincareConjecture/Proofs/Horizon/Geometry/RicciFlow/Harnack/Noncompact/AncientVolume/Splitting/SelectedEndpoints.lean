import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.InitialDirections
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SourceSegments
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.BufferedSegments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace Poincare.AncientVolume.Splitting

theorem exists_small_diverging_radii
    {L D : ℕ → ℝ} (hL : ∀ i, 0 < L i) (hD : ∀ i, 0 < D i)
    (hLtop : Tendsto L atTop atTop) (hDtop : Tendsto D atTop atTop)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ s : ℕ → ℝ, (∀ i, 0 < s i ∧ K * s i ≤ L i ∧ 2 * s i ≤ D i) ∧
      Tendsto s atTop atTop ∧ Tendsto (fun i => s i / L i) atTop (𝓝 0) := by
  let s := fun i => min (Real.sqrt (L i)) (min (L i / (K + 1)) (D i / 2))
  have hs (i : ℕ) : 0 < s i :=
    lt_min (Real.sqrt_pos.mpr (hL i))
      (lt_min (div_pos (hL i) (by linarith)) (div_pos (hD i) (by norm_num)))
  have hsL (i : ℕ) : s i ≤ L i / (K + 1) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hsD (i : ℕ) : s i ≤ D i / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsqrt := Real.tendsto_sqrt_atTop.comp hLtop
  have hdivL := hLtop.atTop_div_const (by linarith : 0 < K + 1)
  have hdivD := hDtop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hstop : Tendsto s atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hsqrt.eventually_ge_atTop b, hdivL.eventually_ge_atTop b,
      hdivD.eventually_ge_atTop b] with i hi hj hk
    exact le_min hi (le_min hj hk)
  refine ⟨s, fun i => ⟨hs i, ?_, by linarith [hsD i]⟩, hstop, ?_⟩
  · have h := (le_div_iff₀ (by linarith : 0 < K + 1)).mp (hsL i)
    nlinarith [hs i]
  · apply squeeze_zero (fun i => div_nonneg (hs i).le (hL i).le) (fun i => ?_)
      (tendsto_const_nhds.div_atTop hsqrt : Tendsto (fun i => 1 / Real.sqrt (L i)) atTop (𝓝 0))
    calc
      s i / L i ≤ Real.sqrt (L i) / L i :=
        div_le_div_of_nonneg_right (min_le_left _ _) (hL i).le
      _ = 1 / Real.sqrt (L i) := by
        have hspos : Real.sqrt (L i) ≠ 0 := (Real.sqrt_pos.mpr (hL i)).ne'
        field_simp [hspos, (hL i).ne']
        exact Real.sq_sqrt (hL i).le

end Poincare.AncientVolume.Splitting

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_trimmed_normalized_opposite_segments
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (p : M) (q y : ℕ → M) (r Q : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hQ : ∀ i, 0 < Q i)
    (hd : ∀ i, 0 < (g.edist p (q i)).toReal)
    (hfar : ∀ i, (g.edist p (q i)).toReal ≤ (g.edist (q i) (y i)).toReal)
    (hDtop : Tendsto (fun i => (g.edist p (q i)).toReal * Real.sqrt (Q i)) atTop atTop)
    (hLtop : Tendsto (fun i => r i * Real.sqrt (Q i)) atTop atTop)
    (hcos : Tendsto (fun i =>
      ((g.edist p (q i)).toReal ^ 2 + (g.edist (q i) (y i)).toReal ^ 2 -
        (g.edist p (y i)).toReal ^ 2) /
          (2 * (g.edist p (q i)).toReal * (g.edist (q i) (y i)).toReal)) atTop (𝓝 (-1)))
    {K : ℝ} (hK : 0 ≤ K)
    (hcomparison : ∀ i (minus plus : ℝ → M) (A B : ℝ), 0 < A → 0 < B →
      minus 0 = q i → minus A = p → plus 0 = q i → plus B = y i →
      (∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) A,
        ((rescaledMetric g (Q i) (hQ i)).edist (minus s) (minus t)).toReal = |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) B, ∀ t ∈ Icc (0 : ℝ) B,
        ((rescaledMetric g (Q i) (hQ i)).edist (plus s) (plus t)).toReal = |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((A ^ 2 + B ^ 2 - ((rescaledMetric g (Q i) (hQ i)).edist p (y i)).toReal ^ 2) /
            (2 * A * B)) ≤
          ((rescaledMetric g (Q i) (hQ i)).edist (minus s) (plus t)).toReal ^ 2) :
    let G := fun i => rescaledMetric g (Q i) (hQ i)
    ∃ s : ℕ → ℝ, ∃ minus plus : ℕ → ℝ → M,
      (∀ i, 0 < s i ∧ K * s i ≤ r i * Real.sqrt (Q i)) ∧
      Tendsto (fun i => s i / (r i * Real.sqrt (Q i))) atTop (𝓝 0) ∧
      Tendsto (fun i => s i / 2) atTop atTop ∧
      (∀ i, minus i 0 = q i ∧ plus i 0 = q i ∧
        minus i (s i / 2) ∈ (G i).ball (q i) (s i) ∧
        plus i (s i / 2) ∈ (G i).ball (q i) (s i)) ∧
      (∀ i, ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
        ((G i).edist (minus i a) (minus i b)).toReal = |a - b|) ∧
      (∀ i, ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
        ((G i).edist (plus i a) (plus i b)).toReal = |a - b|) ∧
      Tendsto (fun i =>
        ((s i / 2) ^ 2 + (s i / 2) ^ 2 -
          ((G i).edist (minus i (s i / 2)) (plus i (s i / 2))).toReal ^ 2) /
            (2 * (s i / 2) * (s i / 2))) atTop (𝓝 (-1)) := by
  let G := fun i => rescaledMetric g (Q i) (hQ i)
  let A := fun i => ((G i).edist (q i) p).toReal
  let B := fun i => ((G i).edist (q i) (y i)).toReal
  have hcomm (g' : RiemannianMetric n M) (x z : M) :
      (g'.edist x z).toReal = (g'.edist z x).toReal := by
    let := g'.toMetricSpace
    exact dist_comm x z
  have hdist (i : ℕ) (x z : M) :
      ((G i).edist x z).toReal = Real.sqrt (Q i) * (g.edist x z).toReal := by
    rw [rescaledMetric_edist, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hA (i : ℕ) : A i = (g.edist p (q i)).toReal * Real.sqrt (Q i) := by
    dsimp only [A]
    rw [hdist, hcomm g (q i) p, mul_comm]
  have hAp (i : ℕ) : 0 < A i := by rw [hA]; exact mul_pos (hd i) (Real.sqrt_pos.mpr (hQ i))
  have hAB (i : ℕ) : A i ≤ B i := by
    rw [hA, show B i = Real.sqrt (Q i) * (g.edist (q i) (y i)).toReal from hdist i _ _]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hfar i) (Real.sqrt_nonneg (Q i))
  have hBp (i : ℕ) : 0 < B i := (hAp i).trans_le (hAB i)
  have hAtop : Tendsto A atTop atTop := hDtop.congr (fun i => (hA i).symm)
  obtain ⟨s, hs, hstop, hsmall⟩ := Poincare.AncientVolume.Splitting.exists_small_diverging_radii
    (fun i => mul_pos (hr i) (Real.sqrt_pos.mpr (hQ i))) hAp hLtop hAtop hK
  have hhalf (i : ℕ) : 0 < s i / 2 := div_pos (hs i).1 (by norm_num)
  have hhalfA (i : ℕ) : s i / 2 ≤ A i := by linarith [(hs i).2.2, (hs i).1]
  have hhalfB (i : ℕ) : s i / 2 ≤ B i := (hhalfA i).trans (hAB i)
  choose minus hm0 hmend hmmin using fun i =>
    (G i).exists_unit_speed_minimizing_segment_of_metricComplete
      (metricComplete_rescaledMetric g (Q i) (hQ i) hcomplete) (q i) p (hAp i)
  choose plus hp0 hpend hpmin using fun i =>
    (G i).exists_unit_speed_minimizing_segment_of_metricComplete
      (metricComplete_rescaledMetric g (Q i) (hQ i) hcomplete) (q i) (y i) (hBp i)
  have hminus (i : ℕ) : ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
      ((G i).edist (minus i a) (minus i b)).toReal = |a - b| :=
    fun a ha b hb => hmmin i a ⟨ha.1, ha.2.trans (hhalfA i)⟩ b ⟨hb.1, hb.2.trans (hhalfA i)⟩
  have hplus (i : ℕ) : ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
      ((G i).edist (plus i a) (plus i b)).toReal = |a - b| :=
    fun a ha b hb => hpmin i a ⟨ha.1, ha.2.trans (hhalfB i)⟩ b ⟨hb.1, hb.2.trans (hhalfB i)⟩
  have hleft (i : ℕ) : ((G i).edist (q i) (minus i (s i / 2))).toReal = s i / 2 := by
    rw [← hm0 i, hminus i 0 ⟨le_rfl, (hhalf i).le⟩ (s i / 2) ⟨(hhalf i).le, le_rfl⟩,
      zero_sub, abs_neg, abs_of_pos (hhalf i)]
  have hright (i : ℕ) : ((G i).edist (q i) (plus i (s i / 2))).toReal = s i / 2 := by
    rw [← hp0 i, hplus i 0 ⟨le_rfl, (hhalf i).le⟩ (s i / 2) ⟨(hhalf i).le, le_rfl⟩,
      zero_sub, abs_neg, abs_of_pos (hhalf i)]
  let oldcos := fun i =>
    (A i ^ 2 + B i ^ 2 - ((G i).edist p (y i)).toReal ^ 2) / (2 * A i * B i)
  have holdcos : Tendsto oldcos atTop (𝓝 (-1)) := by
    apply hcos.congr
    intro i
    symm
    dsimp only [oldcos, A, B]
    rw [hcomm (G i) (q i) p]
    exact g.endpoint_comparison_cosine_rescaledMetric (Q i) (hQ i) p (q i) (y i)
  let newcos := fun i =>
    ((s i / 2) ^ 2 + (s i / 2) ^ 2 -
      ((G i).edist (minus i (s i / 2)) (plus i (s i / 2))).toReal ^ 2) /
        (2 * (s i / 2) * (s i / 2))
  have hlower (i : ℕ) : -1 ≤ newcos i := by
    have htri : ((G i).edist (minus i (s i / 2)) (plus i (s i / 2))).toReal ≤ s i / 2 + s i / 2 := by
      let := (G i).toMetricSpace
      have h := dist_triangle (minus i (s i / 2)) (q i) (plus i (s i / 2))
      change ((G i).edist _ _).toReal ≤ ((G i).edist _ _).toReal + ((G i).edist _ _).toReal at h
      rwa [hcomm (G i) _ (q i), hleft, hright] at h
    dsimp only [newcos]
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) (hhalf i)) (hhalf i))).mpr
    nlinarith [pow_le_pow_left₀ ENNReal.toReal_nonneg htri 2]
  have hupper (i : ℕ) : newcos i ≤ oldcos i := by
    have hcmp := hcomparison i (minus i) (plus i) (A i) (B i) (hAp i) (hBp i)
      (hm0 i) (hmend i) (hp0 i) (hpend i) (hmmin i) (hpmin i)
      (s i / 2) ⟨(hhalf i).le, hhalfA i⟩ (s i / 2) ⟨(hhalf i).le, hhalfB i⟩
    dsimp only [newcos]
    apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) (hhalf i)) (hhalf i))).mpr
    change _ - 2 * (s i / 2) * (s i / 2) * oldcos i ≤ _ at hcmp
    nlinarith
  refine ⟨s, minus, plus, (fun i => ⟨(hs i).1, (hs i).2.1⟩), hsmall,
    hstop.atTop_div_const (by norm_num), ?_, hminus, hplus,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds holdcos hlower hupper⟩
  intro i
  refine ⟨hm0 i, hp0 i, ?_, ?_⟩
  · apply (ENNReal.lt_ofReal_iff_toReal_lt ((G i).edist_ne_top _ _)).mpr
    rw [hleft]
    linarith [(hs i).1]
  · apply (ENNReal.lt_ofReal_iff_toReal_lt ((G i).edist_ne_top _ _)).mpr
    rw [hright]
    linarith [(hs i).1]

set_option maxHeartbeats 800000 in

theorem exists_selected_normalized_opposite_segments_of_comparison
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (p : M) (q : ℕ → M) (r Q : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hQ : ∀ i, 0 < Q i)
    (hdtop : Tendsto (fun i => (g.edist p (q i)).toReal) atTop atTop)
    (hDtop : Tendsto (fun i => (g.edist p (q i)).toReal * Real.sqrt (Q i)) atTop atTop)
    (hLtop : Tendsto (fun i => r i * Real.sqrt (Q i)) atTop atTop)
    (hsmall : Tendsto (fun i => r i / (g.edist p (q i)).toReal) atTop (𝓝 0))
    {K : ℝ} (hK : 0 ≤ K)
    (hhinge : ∀ (x y : M) (ε₁ ε₂ : ℝ) (γ₁ γ₂ : ℝ → M)
      (v w : TangentSpace (𝓡 n) p), 0 < ε₁ → 0 < ε₂ →
      g.IsGeodesicOn γ₁ (Ioo (-ε₁) (1 + ε₁)) →
      g.IsGeodesicOn γ₂ (Ioo (-ε₂) (1 + ε₂)) →
      γ₁ 0 = p → γ₁ 1 = x → γ₂ 0 = p → γ₂ 1 = y →
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        g.edist (γ₁ a) (γ₁ b) = ENNReal.ofReal |a - b| * g.edist p x) →
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        g.edist (γ₂ a) (γ₂ b) = ENNReal.ofReal |a - b| * g.edist p y) →
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ₁ t)) ((g.edist p x).toReal • v) 0 →
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ₂ t)) ((g.edist p y).toReal • w) 0 →
      (g.edist x y).toReal ^ 2 ≤ (g.edist p x).toReal ^ 2 + (g.edist p y).toReal ^ 2 -
        2 * (g.edist p x).toReal * (g.edist p y).toReal * g.inner p v w)
    (hcomparison : ∀ i j (minus plus : ℝ → M) (A B : ℝ), 0 < A → 0 < B →
      minus 0 = q i → minus A = p → plus 0 = q i → plus B = q j →
      (∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) A,
        ((rescaledMetric g (Q i) (hQ i)).edist (minus s) (minus t)).toReal = |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) B, ∀ t ∈ Icc (0 : ℝ) B,
        ((rescaledMetric g (Q i) (hQ i)).edist (plus s) (plus t)).toReal = |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((A ^ 2 + B ^ 2 - ((rescaledMetric g (Q i) (hQ i)).edist p (q j)).toReal ^ 2) /
            (2 * A * B)) ≤
          ((rescaledMetric g (Q i) (hQ i)).edist (minus s) (plus t)).toReal ^ 2) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun i => r (σ i) / (g.edist p (q (σ i))).toReal) atTop (𝓝 0) ∧
      ∃ (ε : ℕ → ℝ) (γ : ℕ → ℝ → M)
        (v : ℕ → TangentSpace (𝓡 n) p) (vlim : TangentSpace (𝓡 n) p),
        (∀ i, 0 < ε i ∧ g.IsGeodesicOn (γ i) (Ioo (-ε i) (1 + ε i)) ∧
          γ i 0 = p ∧ γ i 1 = q (σ i) ∧
          (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
            g.edist (γ i a) (γ i b) = ENNReal.ofReal |a - b| * g.edist p (q (σ i))) ∧
          HasDerivAt (fun t => extChartAt (𝓡 n) p (γ i t))
            ((g.edist p (q (σ i))).toReal • v i) 0 ∧
          g.tangentNorm p (v i) = 1 ∧ 0 < (g.edist p (q (σ i))).toReal) ∧
        Tendsto v atTop (𝓝 vlim) ∧ g.tangentNorm p vlim = 1 ∧
        ∃ k : ℕ → ℕ, (∀ i, i ≤ k i) ∧
          (∀ i, (g.edist p (q (σ i))).toReal * ((i : ℝ) + 2) + 1 ≤
            (g.edist p (q (σ (k i)))).toReal) ∧
          let G := fun i => rescaledMetric g (Q (σ i)) (hQ (σ i))
          ∃ s : ℕ → ℝ, ∃ minus plus : ℕ → ℝ → M,
            (∀ i, 0 < s i ∧ K * s i ≤ r (σ i) * Real.sqrt (Q (σ i))) ∧
            Tendsto (fun i => s i / (r (σ i) * Real.sqrt (Q (σ i)))) atTop (𝓝 0) ∧
            Tendsto (fun i => s i / 2) atTop atTop ∧
            (∀ i, minus i 0 = q (σ i) ∧ plus i 0 = q (σ i) ∧
              minus i (s i / 2) ∈ (G i).ball (q (σ i)) (s i) ∧
              plus i (s i / 2) ∈ (G i).ball (q (σ i)) (s i)) ∧
            (∀ i, ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
              ((G i).edist (minus i a) (minus i b)).toReal = |a - b|) ∧
            (∀ i, ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
              ((G i).edist (plus i a) (plus i b)).toReal = |a - b|) ∧
            Tendsto (fun i =>
              ((s i / 2) ^ 2 + (s i / 2) ^ 2 -
                ((G i).edist (minus i (s i / 2)) (plus i (s i / 2))).toReal ^ 2) /
                  (2 * (s i / 2) * (s i / 2))) atTop (𝓝 (-1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let := g.toMetricSpace
  obtain ⟨σ, hσ, ε, γ, v, vlim, hdata, hv, hvlim, hescape⟩ :=
    g.exists_convergent_initial_directions_of_metricComplete hcomplete p q hdtop
  have hside (i j : ℕ) : dist (q (σ i)) (q (σ j)) ^ 2 ≤
      dist p (q (σ i)) ^ 2 + dist p (q (σ j)) ^ 2 -
        2 * dist p (q (σ i)) * dist p (q (σ j)) * inner ℝ (v i) (v j) := by
    rcases hdata i with ⟨hiε, higeo, hi0, hi1, himin, hider, _hinorm, _hipos⟩
    rcases hdata j with ⟨hjε, hjgeo, hj0, hj1, hjmin, hjder, _hjnorm, _hjpos⟩
    exact hhinge (q (σ i)) (q (σ j)) (ε i) (ε j) (γ i) (γ j) (v i) (v j)
      hiε hjε higeo hjgeo hi0 hi1 hj0 hj1 himin hjmin hider hjder
  obtain ⟨k, hk, hfar, hcos⟩ :=
    Poincare.AncientVolume.Splitting.exists_farther_vertices_of_convergent_directions
      p (fun i => q (σ i)) v (fun i => (hdata i).2.2.2.2.2.2.2)
      hescape hv hvlim hside
  have hfar' (i : ℕ) : (g.edist p (q (σ i))).toReal ≤
      (g.edist (q (σ i)) (q (σ (k i)))).toReal := by
    have htri := dist_triangle p (q (σ i)) (q (σ (k i)))
    have hn := mul_nonneg (dist_nonneg : 0 ≤ dist p (q (σ i)))
      (Nat.cast_nonneg i : 0 ≤ (i : ℝ))
    change dist p (q (σ i)) ≤ dist (q (σ i)) (q (σ (k i)))
    nlinarith [hfar i]
  obtain ⟨s, minus, plus, hs, hsmall', hstop, hbase, hminus, hplus, hangle⟩ :=
    g.exists_trimmed_normalized_opposite_segments hcomplete p (fun i => q (σ i))
      (fun i => q (σ (k i))) (fun i => r (σ i)) (fun i => Q (σ i))
      (fun i => hr (σ i)) (fun i => hQ (σ i)) (fun i => (hdata i).2.2.2.2.2.2.2)
      hfar' (hDtop.comp hσ.tendsto_atTop) (hLtop.comp hσ.tendsto_atTop) hcos hK
      (fun i => hcomparison (σ i) (σ (k i)))
  exact ⟨σ, hσ, hsmall.comp hσ.tendsto_atTop, ε, γ, v, vlim,
    hdata, hv, hvlim, k, hk, hfar, s, minus, plus, hs, hsmall', hstop,
    hbase, hminus, hplus, hangle⟩

end PoincareConjecture.RiemannianMetric
