import PoincareConjecture.Proofs.M25.AppA_21_Local.CapEndWidth

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

theorem ConnectedNeckCapCover.exists_uniform_cap_truncation_depth_gain_of_end_neck_overlap :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (H : ConnectedNeckCapCover g),
      H.epsilon ≤ epsilon0 →
      ∀ (seed : CapCertificate g), seed ∈ H.caps → ∀ (x : M), x ∈ seed.core →
      ∀ (C0 : CapCertificate g), C0 ∈ H.caps → x ∈ C0.core →
      ¬ connectedComponent x ⊆ C0.carrier →
      ∀ (C1 : CapCertificate g), C1 ∈ H.caps →
      (C0.carrier \ C0.end_neck.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆ C1.core) →
      (C0.end_neck.carrier ∩ C1.end_neck.carrier).Nonempty →
      C0.exteriorEDepth x + ENNReal.ofReal
        ((9 / 10) * H.epsilon⁻¹ *
          (H.cap_constant * seed.connection.scalarCurvature x) ^ (-1 / 2 : ℝ)) ≤
        C1.exteriorEDepth x := by
  obtain ⟨epsilon0, hpos, hcap, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := 1 / 10) (by norm_num)
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hH seed _hseed x hxseed C0 hC0 hx0 hproper C1 hC1 hcut hinter
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let L := H.epsilon⁻¹
  let N0 := C0.end_neck
  let N1 := C1.end_neck
  let P0 := N0.region (L / 2) L
  let D0 := C0.carrier \ P0
  let ell := (7 / 10 : ℝ) * L * N0.scale
  let h0 := (H.cap_constant * seed.connection.scalarCurvature x) ^ (-1 / 2 : ℝ)
  let delta := (9 / 10 : ℝ) * L * h0
  let w1 := 2 * L * N1.scale * Real.sqrt (1 - H.epsilon)
  have heps : H.epsilon ≤ 1 / 200 := hH.trans hcap
  have hLpos : 0 < L := inv_pos.mpr H.epsilon_pos
  have hL : 200 ≤ L := by
    have h : (200 : ℝ) ≤ 1 / H.epsilon :=
      (le_div_iff₀ H.epsilon_pos).mpr (by nlinarith)
    simpa only [one_div, L] using h
  have heps0 : C0.epsilon = H.epsilon := H.cap_epsilon C0 hC0
  have heps1 : C1.epsilon = H.epsilon := H.cap_epsilon C1 hC1
  have hN0 : N0.epsilon = H.epsilon := C0.end_neck_epsilon.trans heps0
  have hN1 : N1.epsilon = H.epsilon := C1.end_neck_epsilon.trans heps1
  have ht : L / 2 ∈ Ioo (-C0.epsilon⁻¹) C0.epsilon⁻¹ := by
    rw [heps0]
    change -L < L / 2 ∧ L / 2 < L
    constructor <;> linarith
  have hDcompact : IsCompact D0 := by
    simpa only [D0, P0, N0, L, heps0] using C0.isCompact_end_neck_lower_cut ht
  have htop := C0.end_neck_lower_cut_topology ht
  dsimp only at htop
  have hDinterior : interior D0 = C0.closed_core ∪ N0.region (-L) (L / 2) := by
    simpa only [D0, P0, N0, L, heps0] using htop.2.2.2.1
  have hfront : frontier C0.carrier ⊆ closure P0 := by
    simpa only [P0, N0, L, heps0] using htop.2.2.2.2.2.2
  have hxD : x ∈ interior D0 := by
    rw [hDinterior]
    apply Or.inl
    rw [C0.core_eq_interior_closed_core] at hx0
    exact interior_subset hx0
  have hfrontne : (frontier C0.carrier).Nonempty := by
    by_contra h
    have hclopen : IsClopen C0.carrier :=
      isClopen_iff_frontier_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
    exact hproper (hclopen.connectedComponent_subset (C0.m25_core_subset_carrier hx0))
  obtain ⟨p, hp⟩ := hfrontne
  have hpP : p ∈ closure P0 := hfront hp
  have hpout : p ∉ C0.carrier := by
    rw [C0.carrier_open.frontier_eq] at hp
    exact hp.2
  have hsqrt : Real.sqrt (1 + H.epsilon) ≤ 11 / 10 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hsphere : Real.sqrt 2 * (Real.pi + 1) ≤ 10 := by
    have hs : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hp' : Real.pi + 1 ≤ 5 := by linarith [Real.pi_lt_four]
    have h := mul_le_mul hs hp' (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h ⊢
    exact h
  have hnumeric : (11 / 10 : ℝ) * (L / 2 + 10) ≤ (7 / 10) * L := by
    linarith
  have hdiam (y : M) (hy : y ∈ P0) (z : M) (hz : z ∈ P0) :
      g.edist y z ≤ ENNReal.ofReal ell := by
    have hheight : |(N0.coordinate_inverse z).2 - (N0.coordinate_inverse y).2| ≤ L / 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hy.2.1, hy.2.2, hz.2.1, hz.2.2]
    have h := N0.edist_le_axial_add hy.1 hz.1
    rw [hN0] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have hu := (mul_le_mul hsqrt (add_le_add hheight hsphere)
      (by positivity) (by norm_num : (0 : ℝ) ≤ 11 / 10)).trans hnumeric
    calc
      N0.scale * Real.sqrt (1 + H.epsilon) *
          (|(N0.coordinate_inverse z).2 - (N0.coordinate_inverse y).2| +
            Real.sqrt 2 * (Real.pi + 1)) =
          N0.scale * (Real.sqrt (1 + H.epsilon) *
            (|(N0.coordinate_inverse z).2 - (N0.coordinate_inverse y).2| +
              Real.sqrt 2 * (Real.pi + 1))) := mul_assoc _ _ _
      _ ≤ N0.scale * ((7 / 10) * L) := mul_le_mul_of_nonneg_left hu N0.scale_pos.le
      _ = ell := by dsimp only [ell]; ring
  have htail (y : M) (hy : y ∈ P0) : C0.exteriorEDepth y ≤ ENNReal.ofReal ell := by
    have hclosed : IsClosed {z | g.edist y z ≤ ENNReal.ofReal ell} :=
      isClosed_le (continuous_const.edist continuous_id) continuous_const
    have hdist : g.edist y p ≤ ENNReal.ofReal ell :=
      closure_minimal (hdiam y hy) hclosed hpP
    exact (iInf₂_le p hpout).trans hdist
  have hloss : C0.exteriorEDepth x ≤
      (⨅ y ∈ D0ᶜ, g.edist x y) + ENNReal.ofReal ell := by
    simp only [ENNReal.iInf_add, le_iInf_iff]
    intro y hy
    by_cases hyU : y ∈ C0.carrier
    · have hyP : y ∈ P0 := by
        by_contra hnot
        exact hy ⟨hyU, hnot⟩
      have htriangle : C0.exteriorEDepth x ≤ g.edist x y + C0.exteriorEDepth y :=
        Metric.infEDist_le_edist_add_infEDist
      exact htriangle.trans (add_le_add le_rfl (htail y hyP))
    · have hmem : C0.exteriorEDepth x ≤ g.edist x y := iInf₂_le y hyU
      exact hmem.trans (le_add_of_nonneg_right (by positivity))
  have hx1 : x ∈ C1.core := hcut (interior_subset hxD)
  have hDnew : closure D0 ⊆ C1.closed_core := by
    rw [hDcompact.isClosed.closure_eq]
    apply hcut.trans
    rw [C1.core_eq_interior_closed_core]
    exact interior_subset
  have hwidth := C1.exteriorEDepth_add_end_width_le hxD hDnew
  rw [heps1] at hwidth
  change (⨅ y ∈ D0ᶜ, g.edist x y) + ENNReal.ofReal w1 ≤ C1.exteriorEDepth x at hwidth
  have hscalar : C1.connection.scalarCurvature x = seed.connection.scalarCurvature x := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    simp_rw [C1.connection.horizon_curvatureTensor_eq seed.connection x]
  have hscaleLower := C1.end_neck_scale_lower (C1.m25_core_subset_carrier hx1)
    (H.cap_constant_bound C1 hC1)
  rw [hscalar] at hscaleLower
  change h0 ≤ N1.scale at hscaleLower
  have hh0 : 0 < h0 := Real.rpow_pos_of_pos
    (mul_pos H.cap_constant_pos (seed.scalar_pos x (seed.m25_core_subset_carrier hxseed))) _
  have hdelta : 0 ≤ delta := by dsimp only [delta]; positivity
  have hell : 0 ≤ ell :=
    mul_nonneg (mul_nonneg (by norm_num) hLpos.le) N0.scale_pos.le
  have hclose := (hscale N1 N0 (by rw [hN1]; exact hH)
    (by rw [hN0]; exact hH) (by simpa only [inter_comm] using hinter)).2
  have hratio : N0.scale ≤ (11 / 10) * N1.scale := by
    have hdiv : N0.scale / N1.scale < 11 / 10 := by linarith [(abs_lt.mp hclose).2]
    exact ((div_lt_iff₀ N1.scale_pos).mp hdiv).le
  have hellBound : ell ≤ (77 / 100) * L * N1.scale := by
    calc
      ell ≤ ((7 / 10) * L) * ((11 / 10) * N1.scale) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (77 / 100) * L * N1.scale := by ring
  have hdeltaBound : delta ≤ (9 / 10) * L * N1.scale :=
    mul_le_mul_of_nonneg_left hscaleLower (by positivity)
  have hsqrtLower : (9 / 10 : ℝ) ≤ Real.sqrt (1 - H.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hwidthLower : (9 / 5 : ℝ) * L * N1.scale ≤ w1 := by
    calc
      (9 / 5 : ℝ) * L * N1.scale = (2 * L * N1.scale) * (9 / 10) := by ring
      _ ≤ w1 := mul_le_mul_of_nonneg_left hsqrtLower
        (mul_nonneg (mul_nonneg (by norm_num) hLpos.le) N1.scale_pos.le)
  have hbudget : ell + delta ≤ w1 := by
    calc
      ell + delta ≤ (77 / 100) * L * N1.scale + (9 / 10) * L * N1.scale :=
        add_le_add hellBound hdeltaBound
      _ = (167 / 100) * L * N1.scale := by ring
      _ ≤ (9 / 5) * L * N1.scale := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (167 / 100 : ℝ) ≤ 9 / 5) hLpos.le)
        N1.scale_pos.le
      _ ≤ w1 := hwidthLower
  change C0.exteriorEDepth x + ENNReal.ofReal delta ≤ C1.exteriorEDepth x
  calc
    C0.exteriorEDepth x + ENNReal.ofReal delta ≤
        ((⨅ y ∈ D0ᶜ, g.edist x y) + ENNReal.ofReal ell) + ENNReal.ofReal delta :=
      add_le_add hloss le_rfl
    _ = (⨅ y ∈ D0ᶜ, g.edist x y) + ENNReal.ofReal (ell + delta) := by
      rw [ENNReal.ofReal_add hell hdelta, add_assoc]
    _ ≤ (⨅ y ∈ D0ᶜ, g.edist x y) + ENNReal.ofReal w1 :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal hbudget)
    _ ≤ C1.exteriorEDepth x := hwidth

end PoincareConjecture
