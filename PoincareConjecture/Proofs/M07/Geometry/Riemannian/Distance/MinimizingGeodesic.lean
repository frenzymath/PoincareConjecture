import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingStep
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Minimizing.ExponentialChord
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.GeodesicGrowth

















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in
private theorem norm_smul (g : RiemannianMetric n M) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    g.tangentNorm p (c • v) = |c| * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

omit [T2Space M] in
private theorem chart_speed {g : RiemannianMetric n M} {γ : ℝ → M}
    {S : Set ℝ} (hγ : g.IsGeodesicOn γ S) {t : ℝ} (ht : t ∈ S)
    {v : EuclideanSpace ℝ (Fin n)}
    (hv : HasDerivAt (fun u => extChartAt (𝓡 n) (γ t) (γ u)) v t) :
    g.tangentNorm (γ t) v =
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) := by
  have hc := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞)
    (mem_chart_source _ (γ t))).mdifferentiableAt (by simp)
  have heq := congrArg (fun L => L 1)
    (mfderiv_comp t hc ((hγ.contMDiffAt ht).mdifferentiableAt one_ne_zero))
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun u => extChartAt (𝓡 n) (γ t) (γ u)) t = _ at heq
  rw [hv.deriv] at heq
  change v = (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (γ t)) (γ t))
    (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) at heq
  have hchart := congrArg (fun L => L (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1))
    (mfderiv_extChartAt_self (I := 𝓡 n) (x := γ t))
  exact congrArg (g.tangentNorm (γ t)) (heq.trans hchart)

omit [T2Space M] in
private theorem geodesic_bounds {g : RiemannianMetric n M} {γ : ℝ → M}
    {a b : ℝ} (hγ : g.IsGeodesicOn γ (Ioo a b))
    (h0 : (0 : ℝ) ∈ Ioo a b) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin n)}
    (hv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0) :
    (∀ t ∈ Ioo a b,
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) =
        g.tangentNorm p v) ∧
    (∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      g.edist (γ s) (γ t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p v)) := by
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (h0.1.trans h0.2)
  have hCv : g.tangentNorm p v = (C : ℝ) := by
    have hh := (hγ.tangentNorm_initial h0 hp hv).symm.trans (hC 0 h0)
    simpa only [chartCoefficients_self, tangentNorm] using hh
  refine ⟨fun t ht => (hC t ht).trans hCv.symm, ?_⟩
  intro s hs t ht
  have hh := hγ.edist_le_of_tangentNorm_eq hC hs ht
  rw [hCv, ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_coe_nnreal,
    mul_comm]
  simpa only [edist_dist, Real.dist_eq] using hh



theorem exists_minimizing_geodesic_of_precompact_ball
    (g : RiemannianMetric n M) (p q : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hq : q ∈ g.ball p R) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧
      γ 0 = p ∧ γ 1 = q ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p q := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  rcases eq_or_ne p q with rfl | hpq
  · exact g.exists_minimizing_constant_geodesic p
  have hd : 0 < g.edist p q := edist_pos.mpr hpq
  have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt (hq.trans_le le_top)
  let D := (g.edist p q).toReal
  have hD : 0 < D := ENNReal.toReal_pos (ne_of_gt hd) hfinite
  have hpqD : g.edist p q = ENNReal.ofReal D := (ENNReal.ofReal_toReal hfinite).symm
  have hDR : D < R := ENNReal.toReal_lt_of_lt_ofReal hq
  obtain ⟨v, η, ha, haD, hη, hη0, hηv, hadd⟩ :=
    g.exists_short_minimizing_geodesic_step p q hR hcompact hq hd
  let a := g.tangentNorm p v
  let w := (D / a) • v
  have hw : g.tangentNorm p w = D := by
    rw [norm_smul, abs_of_pos (div_pos hD ha)]
    exact div_mul_cancel₀ D ha.ne'
  have hwR : Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) w w) < R := by
    rw [chartCoefficients_self]
    change g.tangentNorm p w < R
    rwa [hw]
  obtain ⟨ε, hε, γ, hγ, hγ0, hγv, _⟩ :=
    g.exists_geodesic_through_one_of_precompact_ball p hR hcompact w hwR
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨hspeed, hbound⟩ := geodesic_bounds hγ (hI (by simp)) hγ0 hγv
  rw [hw] at hspeed hbound
  have hupper := fun s hs t ht => hbound s (hI hs) t (hI ht)
  let t₀ := a / D
  have ht₀ : t₀ ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos ha hD, ((div_lt_one hD).mpr haD).le⟩
  have hscale : g.IsGeodesicOn (fun u => γ (t₀ * u)) (Icc (0 : ℝ) 1) := by
    intro u hu
    exact hγ.comp_mul t₀ u (hI ⟨mul_nonneg ht₀.1.le hu.1,
      mul_le_one₀ ht₀.2 hu.1 hu.2⟩)
  have hscalev : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ (t₀ * u))) v 0 := by
    have hv0 : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) w (t₀ * 0) := by
      simpa only [mul_zero] using hγv
    have hh := hv0.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul t₀)
    have hvw : t₀ • w = v := by
      dsimp [t₀, w]
      rw [smul_smul, show a / D * (D / a) = 1 by
        field_simp [show a ≠ 0 from ha.ne', hD.ne'],
        one_smul]
    simpa only [Function.comp_def, mul_one, hvw] using hh
  have hηI : g.IsGeodesicOn η (Icc (0 : ℝ) 1) := by
    intro u hu
    exact hη u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hread : γ t₀ = η 1 := by
    simpa only [mul_one] using geodesic_endpoint_eq_of_initial_data hscale hηI
      (by simpa only [mul_zero] using hγ0) hη0 hscalev hηv
  have hinit : g.edist (γ t₀) q = ENNReal.ofReal ((1 - t₀) * D) := by
    apply (ENNReal.add_right_inj (a := ENNReal.ofReal a) ENNReal.ofReal_ne_top).mp
    rw [hread, ← hadd, hpqD,
      ← ENNReal.ofReal_add ha.le (mul_nonneg (sub_nonneg.mpr ht₀.2) hD.le)]
    congr 1
    dsimp [t₀]
    field_simp
    ring
  have hstep : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∀ s ∈ Icc (0 : ℝ) t,
        g.edist p (γ s) = ENNReal.ofReal (s * D) ∧
        g.edist (γ s) q = ENNReal.ofReal ((1 - s) * D)) →
      ∃ u ∈ Ioc t 1, g.edist (γ u) q = ENNReal.ofReal ((1 - u) * D) := by
    intro t ht hprefix
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    obtain ⟨hpt, htq⟩ := hprefix t ⟨ht.1.le, le_rfl⟩
    have htadd : g.edist p (γ t) + g.edist (γ t) q = g.edist p q := by
      rw [hpt, htq, hpqD, ← ENNReal.ofReal_add (mul_nonneg ht.1.le hD.le)
        (mul_nonneg (sub_nonneg.mpr ht.2.le) hD.le)]
      congr 1
      ring
    obtain ⟨r, hr, hrc, hqr⟩ :=
      g.exists_precompact_ball_of_edist_add_eq p (γ t) q hcompact hq htadd
    obtain ⟨vb, β, hb, hbsmall, hβ, hβ0, hβv, hβadd⟩ :=
      g.exists_short_minimizing_geodesic_step (γ t) q hr hrc hqr
        (by rw [htq]; exact ENNReal.ofReal_pos.mpr (mul_pos (sub_pos.mpr ht.2) hD))
    let b := g.tangentNorm (γ t) vb
    have hbrem : b < (1 - t) * D := by
      simpa only [htq, ENNReal.toReal_ofReal
        (mul_nonneg (sub_nonneg.mpr ht.2.le) hD.le)] using hbsmall
    have hβI : g.IsGeodesicOn β (Icc (0 : ℝ) 1) := by
      intro u hu
      exact hβ u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    obtain ⟨_, hβbd⟩ := geodesic_bounds hβ (by norm_num) hβ0 hβv
    have hβupper := fun s (hs : s ∈ Icc (0 : ℝ) 1) u (hu : u ∈ Icc (0 : ℝ) 1) =>
      hβbd s ⟨by linarith [hs.1], by linarith [hs.2]⟩
        u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hβqfin : g.edist (β 1) q ≠ ⊤ := by
      apply ne_top_of_le_ne_top (ne_top_of_lt (hqr.trans_le le_top))
      rw [hβadd]
      exact le_add_left le_rfl
    have hbroken : g.edist p (β 1) = ENNReal.ofReal (t * D + b) := by
      apply le_antisymm
      · have hh := edist_triangle p (γ t) (β 1)
        change g.edist p (β 1) ≤ g.edist p (γ t) + g.edist (γ t) (β 1) at hh
        have hbup : g.edist (γ t) (β 1) ≤ ENNReal.ofReal b := by
          simpa only [hβ0, zero_sub, abs_neg, abs_one, one_mul] using
            hβupper 0 (by simp) 1 (by simp)
        exact (hh.trans (add_le_add hpt.le hbup)).trans_eq
          (ENNReal.ofReal_add (mul_nonneg ht.1.le hD.le) hb.le).symm
      · apply ENNReal.le_of_add_le_add_right hβqfin
        rw [ENNReal.ofReal_add (mul_nonneg ht.1.le hD.le) hb.le,
          add_assoc, ← hβadd, ← hpt, htadd]
        exact edist_triangle p (β 1) q
    let wt := deriv (fun s => extChartAt (𝓡 n) (γ t) (γ s)) t
    have hwt := (hγ.hasDerivAt_chart_at (hI htI) (γ t) (mem_extChartAt_source _)).1
    have hwtD : g.tangentNorm (γ t) wt = D :=
      (chart_speed hγ (hI htI) hwt).trans (hspeed t (hI htI))
    let α := fun s => γ (-t * s + t)
    have hbackI (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : -t * s + t ∈ Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]
    have hα : g.IsGeodesicOn α (Icc (0 : ℝ) 1) := by
      intro s hs
      exact hγ.comp_affine (-t) t s (hI (hbackI s hs))
    have hα0 : α 0 = γ t := by simp [α]
    have hα1 : α 1 = p := by simp [α, hγ0]
    have hαv : HasDerivAt (fun s => extChartAt (𝓡 n) (γ t) (α s)) ((-t) • wt) 0 := by
      have hh : HasDerivAt (fun s => extChartAt (𝓡 n) (γ t) (γ s)) wt (-t * 0 + t) := by
        simpa only [mul_zero, zero_add] using hwt
      simpa! only [Function.comp_def, id_eq, mul_one, α] using
        hh.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul (-t)).add_const t)
    have hAnorm : g.tangentNorm (γ t) ((-t) • wt) = t * D := by
      rw [norm_smul, abs_neg, abs_of_pos ht.1, hwtD]
    have hαupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        g.edist (α s) (α u) ≤ ENNReal.ofReal (|s - u| * g.tangentNorm (γ t) ((-t) • wt)) := by
      intro s hs u hu
      have hh := hupper (-t * s + t) (hbackI s hs) (-t * u + t) (hbackI u hu)
      rw [show (-t * s + t) - (-t * u + t) = -t * (s - u) by ring,
        abs_mul, abs_neg, abs_of_pos ht.1] at hh
      simpa only [α, hAnorm, mul_assoc, mul_comm, mul_left_comm] using hh
    have hdir := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics (γ t)
      hα hβI hα0 hβ0 hαv hβv (by rw [hAnorm]; exact mul_pos ht.1 hD) hb
      hαupper hβupper (by rw [hα1, hAnorm]; exact hbroken)
    have hvb : vb = (b / D) • wt := by
      rw [hAnorm, smul_smul, ← neg_smul] at hdir
      have hscalar : -((t * D)⁻¹ * -t) = D⁻¹ := by field_simp [ht.1.ne', hD.ne']
      rw [hscalar] at hdir
      change b⁻¹ • vb = D⁻¹ • wt at hdir
      have hh := congrArg (fun z => b • z) hdir
      simpa only [smul_smul, mul_inv_cancel₀ (show b ≠ 0 from hb.ne'), one_smul,
        ← div_eq_mul_inv] using hh
    let k := b / D
    have hk : 0 < k := div_pos hb hD
    have htk : t + k < 1 := by
      have hh : k < 1 - t := (div_lt_iff₀ hD).mpr hbrem
      linarith
    have hfwd : g.IsGeodesicOn (fun s => γ (k * s + t)) (Icc (0 : ℝ) 1) := by
      intro s hs
      exact hγ.comp_affine k t s (hI ⟨by nlinarith [ht.1, hs.1],
        by nlinarith [hs.2]⟩)
    have hfwdv : HasDerivAt (fun s => extChartAt (𝓡 n) (γ t) (γ (k * s + t))) vb 0 := by
      have hh : HasDerivAt (fun s => extChartAt (𝓡 n) (γ t) (γ s)) wt (k * 0 + t) := by
        simpa only [mul_zero, zero_add] using hwt
      simpa! only [Function.comp_def, id_eq, mul_one, k, ← hvb] using
        hh.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul k).add_const t)
    have hreadβ : γ (t + k) = β 1 := by
      simpa only [mul_one, add_comm] using geodesic_endpoint_eq_of_initial_data
        hfwd hβI (by simp) hβ0 hfwdv hβv
    refine ⟨t + k, ⟨by linarith, htk.le⟩, ?_⟩
    apply (ENNReal.add_right_inj (a := ENNReal.ofReal b) ENNReal.ofReal_ne_top).mp
    rw [hreadβ, ← hβadd, htq, ← ENNReal.ofReal_add hb.le
      (mul_nonneg (sub_nonneg.mpr htk.le) hD.le)]
    congr 1
    dsimp [k]
    field_simp
    ring
  obtain ⟨hγ1, hmin⟩ := PoincareConjecture.edist_segment_of_local_growth hD.le hγ0 hpqD
    hupper ht₀ hinit hstep
  refine ⟨ε, hε, γ, hγ, hγ0, hγ1, ?_⟩
  intro s hs t ht
  rw [hpqD, ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact hmin s hs t ht

end PoincareConjecture.RiemannianMetric
