import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.AngularDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Connected








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8

open Set Filter MeasureTheory TopologicalSpace PoincareConjecture
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hc : RayComparison p}


def unitSliceAngle (x y : AsymptoticConeUnitSlice p hc) : ℝ :=
  Real.arccos (1 - dist x y ^ 2 / 2)

theorem unitSlice_dist_le_two (x y : AsymptoticConeUnitSlice p hc) : dist x y ≤ 2 :=
  asymptoticConeUnitSlice_dist_le_two hc x y

theorem unitSliceAngle_nonneg (x y : AsymptoticConeUnitSlice p hc) : 0 ≤ unitSliceAngle x y :=
  Real.arccos_nonneg _

theorem unitSliceAngle_le_pi (x y : AsymptoticConeUnitSlice p hc) : unitSliceAngle x y ≤ Real.pi :=
  Real.arccos_le_pi _

theorem cos_unitSliceAngle (x y : AsymptoticConeUnitSlice p hc) :
    Real.cos (unitSliceAngle x y) = 1 - dist x y ^ 2 / 2 := by
  apply Real.cos_arccos
  · nlinarith [unitSlice_dist_le_two x y, dist_nonneg (x := x) (y := y)]
  · nlinarith [sq_nonneg (dist x y)]

theorem unitSliceAngle_eq_zero_iff (x y : AsymptoticConeUnitSlice p hc) :
    unitSliceAngle x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hh := cos_unitSliceAngle x y
    rw [h, Real.cos_zero] at hh
    exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := y)])
  · rintro rfl
    simp [unitSliceAngle]

private theorem unit_radial_cosine (x z : AsymptoticConeUnitSlice p hc) (r : ℝ≥0) :
    dist x.1 (asymptoticConeDilation hc r z.1) ^ 2 =
      (r : ℝ) ^ 2 + 1 - 2 * r * Real.cos (unitSliceAngle x z) := by
  rw [dist_sq_asymptoticConeDilation, x.property, z.property, cos_unitSliceAngle]
  change (r : ℝ) ^ 2 * (1 : ℝ) ^ 2 + 1 ^ 2 - r * (1 ^ 2 + 1 ^ 2 - dist x z ^ 2) = _
  ring



theorem unitSliceAngle_triangle (x z y : AsymptoticConeUnitSlice p hc) :
    unitSliceAngle x y ≤ unitSliceAngle x z + unitSliceAngle z y := by
  by_cases hx : x = z
  · subst z
    simp [unitSliceAngle]
  by_cases hy : y = z
  · subst z
    simp [unitSliceAngle]
  let A := unitSliceAngle x z
  let B := unitSliceAngle y z
  have hA : 0 < A := lt_of_le_of_ne (unitSliceAngle_nonneg x z)
    (Ne.symm (mt (unitSliceAngle_eq_zero_iff x z).mp hx))
  have hB : 0 < B := lt_of_le_of_ne (unitSliceAngle_nonneg y z)
    (Ne.symm (mt (unitSliceAngle_eq_zero_iff y z).mp hy))
  have hcomm : unitSliceAngle z y = B := by simp only [B, unitSliceAngle, dist_comm z y]
  rw [hcomm]
  change unitSliceAngle x y ≤ A + B
  by_cases hlarge : Real.pi ≤ A + B
  · exact (unitSliceAngle_le_pi x y).trans hlarge
  have hsum : A + B < Real.pi := lt_of_not_ge hlarge
  have hu : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA (by linarith)
  have hv : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB (by linarith)
  let S := Real.sin A + Real.sin B
  have hS : 0 < S := add_pos hu hv
  let r := (Real.cos A * Real.sin B + Real.cos B * Real.sin A) / S
  have hr : 0 < r := by
    apply div_pos _ hS
    have hh := Real.sin_pos_of_pos_of_lt_pi (add_pos hA hB) hsum
    rw [Real.sin_add] at hh
    nlinarith only [hh]
  let R : ℝ≥0 := ⟨r, hr.le⟩
  let w := asymptoticConeDilation hc R z.1
  let L := Real.sqrt ((Real.cos A - Real.cos B) ^ 2 + S ^ 2)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hL2 : L ^ 2 = (Real.cos A - Real.cos B) ^ 2 + S ^ 2 := Real.sq_sqrt (by positivity)
  have hRA : r - Real.cos A = Real.sin A * (Real.cos B - Real.cos A) / S := by
    dsimp only [r, S]
    field_simp
    ring
  have hRB : r - Real.cos B = Real.sin B * (Real.cos A - Real.cos B) / S := by
    dsimp only [r, S]
    field_simp
    ring
  have hdistA : dist x.1 w = Real.sin A / S * L := by
    have hh := unit_radial_cosine x z R
    change dist x.1 w ^ 2 = r ^ 2 + 1 - 2 * r * Real.cos A at hh
    have hsquare : dist x.1 w ^ 2 = (Real.sin A / S * L) ^ 2 := by
      calc
        _ = (r - Real.cos A) ^ 2 + Real.sin A ^ 2 := by nlinarith only [hh, Real.sin_sq_add_cos_sq A]
        _ = _ := by rw [hRA, mul_pow, hL2]; field_simp; ring
    nlinarith only [hsquare, dist_nonneg (x := x.1) (y := w), mul_nonneg (div_pos hu hS).le hL]
  have hdistB : dist y.1 w = Real.sin B / S * L := by
    have hh := unit_radial_cosine y z R
    change dist y.1 w ^ 2 = r ^ 2 + 1 - 2 * r * Real.cos B at hh
    have hsquare : dist y.1 w ^ 2 = (Real.sin B / S * L) ^ 2 := by
      calc
        _ = (r - Real.cos B) ^ 2 + Real.sin B ^ 2 := by nlinarith only [hh, Real.sin_sq_add_cos_sq B]
        _ = _ := by rw [hRB, mul_pow, hL2]; field_simp
    nlinarith only [hsquare, dist_nonneg (x := y.1) (y := w), mul_nonneg (div_pos hv hS).le hL]
  have hchord : dist x y ≤ L := by
    have hh := dist_triangle x.1 w y.1
    rw [dist_comm w y.1, hdistA, hdistB] at hh
    have htotal : Real.sin A / S * L + Real.sin B / S * L = L := by
      rw [← add_mul, ← add_div, show Real.sin A + Real.sin B = S from rfl, div_self hS.ne', one_mul]
    exact hh.trans_eq htotal
  have hLcos : L ^ 2 = 2 - 2 * Real.cos (A + B) := by
    rw [Real.cos_add]
    dsimp only [S] at hL2
    nlinarith only [hL2, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]
  have hcos : Real.cos (A + B) ≤ 1 - dist x y ^ 2 / 2 := by
    nlinarith only [hLcos, sq_le_sq₀ (dist_nonneg (x := x) (y := y)) hL |>.mpr hchord]
  exact (Real.arccos_le_arccos hcos).trans_eq (Real.arccos_cos (add_pos hA hB).le hsum.le)

theorem unitSliceAngle_eq_twice_arcsin (x y : AsymptoticConeUnitSlice p hc) :
    unitSliceAngle x y = 2 * Real.arcsin (dist x y / 2) := by
  have hlow : -(1 : ℝ) ≤ dist x y / 2 := by linarith [dist_nonneg (x := x) (y := y)]
  have hhigh : dist x y / 2 ≤ 1 := by linarith [unitSlice_dist_le_two x y]
  have hcos : Real.cos (2 * Real.arcsin (dist x y / 2)) = 1 - dist x y ^ 2 / 2 := by
    rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (Real.arcsin (dist x y / 2)),
      Real.sin_arcsin hlow hhigh]
    ring
  change Real.arccos _ = _
  rw [← hcos]
  apply Real.arccos_cos
  · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (div_nonneg dist_nonneg (by norm_num)))
  · linarith [Real.arcsin_le_pi_div_two (dist x y / 2)]



theorem exists_unitSliceAngle_le_mul_dist {c : ℝ} (hc1 : 1 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : AsymptoticConeUnitSlice p hc,
      dist x y < δ → unitSliceAngle x y ≤ c * dist x y := by
  let f := fun s : ℝ => 2 * Real.arcsin (s / 2)
  have hd : HasDerivAt f 1 0 := by
    have h0 : HasDerivAt Real.arcsin 1 (id (0 : ℝ) / 2) := by
      simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
    have hh := (h0.comp 0 ((hasDerivAt_id (0 : ℝ)).div_const 2)).const_mul 2
    simpa [f] using hh
  have hlim : Tendsto (fun s : ℝ => f s / s) (𝓝[>] 0) (𝓝 1) := by
    simpa [f, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, f s / s < c := hlim.eventually (gt_mem_nhds hc1)
  obtain ⟨δ, hδ, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hsmall
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  by_cases heq : x = y
  · subst y
    simp [unitSliceAngle]
  have hpos : 0 < dist x y := dist_pos.mpr heq
  have hh := hsub ⟨hpos, hxy⟩
  rw [unitSliceAngle_eq_twice_arcsin]
  exact ((div_lt_iff₀ hpos).mp hh).le

private theorem ennreal_le_of_real_factors {a b : ℝ≥0∞}
    (h : ∀ c : ℝ, 1 < c → a ≤ ENNReal.ofReal c * b) : a ≤ b := by
  by_cases hb : b = ⊤
  · simp [hb]
  have hfinite : ENNReal.ofReal (2 : ℝ) * b ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hfinite (h 2 (by norm_num))
  apply (ENNReal.toReal_le_toReal ha hb).mp
  apply (le_iff_forall_one_lt_le_mul₀ ENNReal.toReal_nonneg).mpr
  intro c hc
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) (h c hc)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ c)] at hh
  simpa only [mul_comm] using hh



theorem unitSliceAngle_le_pathELength {n : ℕ}
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ γ : ℝ → AsymptoticConeUnitSlice p hc, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ →
      ENNReal.ofReal (unitSliceAngle (γ 0) (γ 1)) ≤ (unitSliceMetric hcover).pathELength γ 0 1 := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  intro γ hγ
  let g := unitSliceMetric hcover
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) := ⟨g.toRiemannianMetric⟩
  apply ennreal_le_of_real_factors
  intro c hc1
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨δ, hδ, hangle⟩ := exists_unitSliceAngle_le_mul_dist (hc := hc) hc1
  let U := fun s : unitInterval => (fun t : unitInterval => γ t) ⁻¹' Metric.ball (γ s) (δ / 2)
  have hUopen : ∀ s, IsOpen (U s) := fun s =>
    Metric.isOpen_ball.preimage (hγ.continuous.comp continuous_subtype_val)
  have hUcover : univ ⊆ ⋃ s, U s := by
    intro s _
    apply mem_iUnion.mpr
    exact ⟨s, by change dist (γ s) (γ s) < δ / 2; rw [dist_self]; positivity⟩
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hUopen hUcover
  have hstep (k : ℕ) : ENNReal.ofReal (unitSliceAngle (γ (t k)) (γ (t (k + 1)))) ≤
      ENNReal.ofReal c * g.pathELength γ (t k) (t (k + 1)) := by
    obtain ⟨s, hts⟩ := hsub k
    have htime : (t k : ℝ) ≤ t (k + 1) := htmono (Nat.le_succ k)
    have hleft : dist (γ (t k)) (γ s) < δ / 2 := hts ⟨le_rfl, htime⟩
    have hright : dist (γ (t (k + 1))) (γ s) < δ / 2 := hts ⟨htime, le_rfl⟩
    have hshort : dist (γ (t k)) (γ (t (k + 1))) < δ := by
      have hh := dist_triangle (γ (t k)) (γ s) (γ (t (k + 1)))
      rw [dist_comm (γ s) (γ (t (k + 1)))] at hh
      linarith
    have hchord : edist (γ (t k)) (γ (t (k + 1))) ≤ g.pathELength γ (t k) (t (k + 1)) :=
      (unitSlice_edist_le_metric_edist hcover _ _).trans
        (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl htime)
    calc
      _ ≤ ENNReal.ofReal (c * dist (γ (t k)) (γ (t (k + 1)))) :=
        ENNReal.ofReal_le_ofReal (hangle _ _ hshort)
      _ = ENNReal.ofReal c * edist (γ (t k)) (γ (t (k + 1))) := by
        rw [ENNReal.ofReal_mul hc0, edist_dist]
      _ ≤ _ := by gcongr
  have hind (k : ℕ) : ENNReal.ofReal (unitSliceAngle (γ 0) (γ (t k))) ≤
      ENNReal.ofReal c * g.pathELength γ 0 (t k) := by
    induction k with
    | zero =>
        rw [ht0]
        change ENNReal.ofReal (unitSliceAngle (γ 0) (γ 0)) ≤ _
        rw [(unitSliceAngle_eq_zero_iff _ _).mpr rfl, ENNReal.ofReal_zero]
        exact bot_le
    | succ k ih =>
        calc
          _ ≤ ENNReal.ofReal (unitSliceAngle (γ 0) (γ (t k)) +
              unitSliceAngle (γ (t k)) (γ (t (k + 1)))) :=
            ENNReal.ofReal_le_ofReal (unitSliceAngle_triangle _ _ _)
          _ = ENNReal.ofReal (unitSliceAngle (γ 0) (γ (t k))) +
              ENNReal.ofReal (unitSliceAngle (γ (t k)) (γ (t (k + 1)))) :=
            ENNReal.ofReal_add (unitSliceAngle_nonneg _ _) (unitSliceAngle_nonneg _ _)
          _ ≤ ENNReal.ofReal c * g.pathELength γ 0 (t k) +
              ENNReal.ofReal c * g.pathELength γ (t k) (t (k + 1)) := add_le_add ih (hstep k)
          _ = _ := by
            rw [← mul_add]
            congr 1
            exact Manifold.pathELength_add (I := 𝓡 n) (γ := γ)
              (t k).property.1 (htmono (Nat.le_succ k))
  have hfinal := hind N
  rw [hN N le_rfl] at hfinal
  exact hfinal



theorem unitSliceAngle_le_metric_edist {n : ℕ}
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ x y : AsymptoticConeUnitSlice p hc,
      ENNReal.ofReal (unitSliceAngle x y) ≤ (unitSliceMetric hcover).edist x y := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  intro x y
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) :=
    ⟨(unitSliceMetric hcover).toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := 𝓡 n) hr zero_lt_one
  have hle := unitSliceAngle_le_pathELength hcover γ hγ
  rw [h0, h1] at hle
  exact hle.trans_lt hlen



theorem unitSlice_metric_edist_eq_angle_of_metric_segment {n : ℕ}
    (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x)
    (x y : AsymptoticConeUnitSlice p hc) (hxy : dist x y < 2)
    (γ : ℝ → AsymptoticCone p hc) (hγ0 : γ 0 = x.1) (hγ1 : γ 1 = y.1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    (unitSliceMetric hcover).edist x y = ENNReal.ofReal (unitSliceAngle x y) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  exact le_antisymm
    (unitSlice_metric_edist_le_angle_of_metric_segment hcover x y hxy γ hγ0 hγ1 hγ)
    (unitSliceAngle_le_metric_edist hcover x y)

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio

private theorem exists_distinct_nearby_link_point
    {n : ℕ} (hn : 1 ≤ n) {S : Type*} [MetricSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S] (x : S) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : S, y ≠ x ∧ dist x y < ε := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let : PerfectSpace (EuclideanSpace ℝ (Fin n)) := perfectSpace_of_module ℝ _
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hxe : e x ∈ e.target := e.map_source hx
  have hball : e.symm ⁻¹' Metric.ball x ε ∈ 𝓝 (e x) := by
    apply (e.continuousAt_symm hxe).preimage_mem_nhds
    simpa only [e.left_inv hx] using Metric.ball_mem_nhds x hε
  obtain ⟨u, hu, hune⟩ := nhdsWithin_neBot.mp
    (inferInstance : NeBot (𝓝[≠] (e x)))
    (inter_mem (e.open_target.mem_nhds hxe) hball)
  have hneq : u ≠ e x := by simpa using hune
  refine ⟨e.symm u, ?_, ?_⟩
  · intro h
    exact hneq ((e.right_inv hu.1).symm.trans (congrArg e h))
  · simpa only [mem_preimage, Metric.mem_ball, dist_comm] using hu.2




theorem unitSlice_metric_edist_eq_angle_of_metricComplete
    {m n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [NoncompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
    (g : RiemannianMetric m M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) (hn : 1 ≤ n) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x,
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ x y : AsymptoticConeUnitSlice p hc,
      (unitSliceMetric hcover).edist x y = ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2)) := by
  let := g.toMetricSpace
  dsimp only
  intro hcover
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let gL := unitSliceMetric hcover
  intro x y
  apply le_antisymm _ (unitSliceAngle_le_metric_edist hcover x y)
  have hshort (z : AsymptoticConeUnitSlice p hc) (hxz : dist x z < 2) :
      gL.edist x z ≤ ENNReal.ofReal (Real.arccos (1 - dist x z ^ 2 / 2)) :=
    g.unitSlice_metric_edist_le_angle_of_metricComplete D hcomplete hsec p hcover x z hxz
  by_cases hxy : dist x y < 2
  · exact hshort y hxy
  have hxy2 : dist x y = 2 := le_antisymm (unitSlice_dist_le_two x y) (le_of_not_gt hxy)
  have hangle : Real.arccos (1 - dist x y ^ 2 / 2) = Real.pi := by
    rw [hxy2]
    norm_num
  change gL.edist x y ≤ ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2))
  rw [hangle]
  let A := {z : AsymptoticConeUnitSlice p hc | gL.edist x z ≤ ENNReal.ofReal Real.pi}
  have hA : IsClosed A := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) := ⟨gL.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : AsymptoticConeUnitSlice p hc → Type _) :=
      ⟨⟨gL.inner, gL.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace (AsymptoticConeUnitSlice p hc) := EMetricSpace.ofRiemannianMetric (𝓡 n) _
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hyA : y ∈ closure A := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨z, hzy, hyz⟩ := exists_distinct_nearby_link_point hn y hε
    have hbound := g.asymptoticConeUnitSlice_dist_sq_add_le_four_of_antipodal
      D hcomplete hsec p x y z hxy2
    have hpos : 0 < dist y z := dist_pos.mpr hzy.symm
    have hxz : dist x z < 2 := by nlinarith [dist_nonneg (x := x) (y := z)]
    refine ⟨z, ?_, ?_⟩
    · exact (hshort z hxz).trans (ENNReal.ofReal_le_ofReal (Real.arccos_le_pi _))
    · simpa only [dist_comm] using hyz
  change y ∈ A
  rwa [hA.closure_eq] at hyA

end PoincareConjecture.RiemannianMetric

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.AncientVolume.ScalarRatio




theorem unitSliceMetric_edist_eq_angle_of_zero_ratio
    {n : ℕ} (hn : 1 ≤ n) {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (n + 1)) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hc := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ x y : AsymptoticConeUnitSlice p hc,
      (unitSliceMetric hcover).edist x y = ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2)) := by
  let := (F.metric t₀).toMetricSpace
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  exact (F.metric t₀).unitSlice_metric_edist_eq_angle_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p hn hcover

end PoincareConjecture.RicciFlow
