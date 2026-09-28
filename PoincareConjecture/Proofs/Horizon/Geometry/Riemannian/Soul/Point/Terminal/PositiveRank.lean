import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.NormalModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_nonzero_centered_geodesic_of_two_points
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ q ∈ S, ∃ (γ : ℝ → M) (v : EuclideanSpace ℝ (Fin n)),
      g.IsGeodesicOn γ (Icc (-(1 / 2) : ℝ) (1 / 2)) ∧ γ 0 = q ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) q (γ t)) v 0 ∧ v ≠ 0 ∧
      MapsTo γ (Icc (-(1 / 2) : ℝ) (1 / 2)) S := by
  obtain ⟨ε, hε, σ, hσ, hσ0, hσ1, _⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hcomplete x y
  let γ : ℝ → M := fun t => σ (t + 1 / 2)
  let q : M := γ 0
  have hunit : g.IsGeodesicOn σ (Icc (0 : ℝ) 1) := by
    intro t ht
    exact hσ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hγ : g.IsGeodesicOn γ (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    intro t ht
    exact hunit.comp_add (1 / 2) t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hleft : γ (-(1 / 2)) = x := by norm_num [γ, hσ0]
  have hright : γ (1 / 2) = y := by norm_num [γ, hσ1]
  have hzero : (0 : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by norm_num
  have hmem : MapsTo γ (Icc (-(1 / 2) : ℝ) (1 / 2)) S :=
    hconv γ (-(1 / 2)) (1 / 2) hγ (hleft.symm ▸ hx) (hright.symm ▸ hy)
  let v := deriv (fun t => extChartAt (𝓡 n) q (γ t)) 0
  have hconstant := g.isGeodesicOn_const q (Icc (-(1 / 2) : ℝ) (1 / 2))
  have hsource : γ 0 ∈ (extChartAt (𝓡 n) q).source := mem_extChartAt_source q
  obtain ⟨U, hU, h0U, hγU, _, hγmap, _⟩ :=
    hγ.exists_common_chart_nhds hconstant hzero q hsource (mem_extChartAt_source q)
  have hd : HasDerivAt (fun t => extChartAt (𝓡 n) q (γ t)) v 0 :=
    (hγU.hasDerivAt_in_chart hU q hγmap 0 h0U).1
  have hv : v ≠ 0 := by
    intro hz
    have hvel : deriv (fun t => extChartAt (𝓡 n) q (γ t)) 0 =
        deriv (fun _ : ℝ => extChartAt (𝓡 n) q q) 0 := by
      simpa only [deriv_const] using hz
    have heq := hγ.eq_nhds_on_of_initial_data hconstant
      (convex_Icc _ _).isPreconnected hzero q hsource rfl hvel
    have hxq : x = q := by
      simpa only [hleft] using (heq (-(1 / 2)) (by norm_num)).self_of_nhds
    have hyq : y = q := by
      simpa only [hright] using (heq (1 / 2) (by norm_num)).self_of_nhds
    exact hxy (hxq.trans hyq.symm)
  exact ⟨q, hmem hzero, γ, v, hγ, rfl, hd, hv, hmem⟩

theorem exists_positive_normal_line_disk_of_two_points
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ q ∈ S, ∃ (r : ℝ)
      (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
      (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
      0 < r ∧ e.source = Metric.ball 0 r ∧ e 0 = q ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      HasFDerivAt (fun v => extChartAt (𝓡 n) q (e v))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 ∧
      (∀ v ∈ Metric.ball 0 r,
        g.IsGeodesicOn (fun t : ℝ => e (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 r}) ∧
      Module.finrank ℝ V = 1 ∧
      e '' (Metric.ball 0 r ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) ⊆ S := by
  obtain ⟨q, hq, γ, v, hγ, hγ0, hd, hv, hmem⟩ :=
    g.exists_nonzero_centered_geodesic_of_two_points hcomplete hconv hx hy hxy
  obtain ⟨φ, hφ0, hφq, hφ, hφi, hφd, Γ, _, hΓ⟩ := g.exists_exponential_chart q
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (φ.open_source.mem_nhds hφ0)
  have hexp : ∀ w ∈ Metric.ball 0 a, ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ → M,
      g.IsGeodesicOn η (Ioo (-ε) (1 + ε)) ∧ η 0 = q ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) q (η t)) w 0 ∧ η 1 = φ w := by
    intro w hw
    have hwΓ := hΓ w (hball hw)
    obtain ⟨hgeo, h0, hderiv⟩ := g.geodesic_of_coordinate_exponential q
      (fun t => Γ (w, t)) w hwΓ.1
      (fun t ht => ⟨(hwΓ.2.2.2 t ht).1, (hwΓ.2.2.2 t ht).2.1⟩)
    refine ⟨1 / 2, by norm_num, fun t => (extChartAt (𝓡 n) q).symm (Γ (w, t)).1,
      ?_, h0, hderiv, hwΓ.2.1⟩
    intro t ht
    exact hgeo t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let r : ℝ := min a (‖v‖ / 2)
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hr : 0 < r := lt_min ha (half_pos hnorm)
  have hra : r ≤ a := min_le_left _ _
  have hrnorm : r ≤ ‖v‖ / 2 := min_le_right _ _
  have hrball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ φ.source :=
    (ball_subset_ball hra).trans hball
  let e := φ.restrOpen (Metric.ball 0 r) isOpen_ball
  have hsource : e.source = Metric.ball 0 r := inter_eq_right.mpr hrball
  refine ⟨q, hq, r, e, Submodule.span ℝ {v}, hr, hsource, hφq,
    hφ.mono inter_subset_left, hφi.mono inter_subset_left, hφd, ?_,
    finrank_span_singleton hv, ?_⟩
  · intro w hw
    have hrad := isGeodesicOn_radial_of_initial_data q
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) φ hexp
      (ball_subset_ball hra hw)
    exact fun t ht => hrad t (ball_subset_ball hra ht)
  · rintro z ⟨w, ⟨hw, hW⟩, rfl⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hW
    have hs : |s| < 1 / 2 := by
      have hsmall := mem_ball_zero_iff.mp hw
      rw [norm_smul, Real.norm_eq_abs] at hsmall
      nlinarith
    obtain ⟨ε, hε, η, hη, hη0, hηd, hη1⟩ := hexp (s • v) (ball_subset_ball hra hw)
    have hscale : g.IsGeodesicOn (fun u => γ (s * u)) (Icc (0 : ℝ) 1) := by
      intro u hu
      apply hγ.comp_mul s u
      change s * u ∈ Icc (-(1 / 2) : ℝ) (1 / 2)
      apply abs_le.mp
      rw [abs_mul, abs_of_nonneg hu.1]
      exact (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg s)).trans
        (by simpa only [mul_one] using hs.le)
    have hηunit : g.IsGeodesicOn η (Icc (0 : ℝ) 1) := by
      intro u hu
      exact hη u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hdscale : HasDerivAt (fun u => extChartAt (𝓡 n) q (γ (s * u)))
        (s • v) 0 := by
      have hd' : HasDerivAt (fun u => extChartAt (𝓡 n) q (γ u)) v (s * 0) := by
        simpa only [mul_zero] using hd
      simpa only [Function.comp_def, id_eq, mul_one] using!
        hd'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul s)
    have heq := hscale.eq_nhds_on_of_initial_data hηunit
      (convex_Icc _ _).isPreconnected (t₀ := 0) (by simp) q
      (by simpa only [mul_zero, hγ0] using mem_extChartAt_source q)
      (by simpa only [mul_zero, hγ0] using hη0.symm)
      (hdscale.deriv.trans hηd.deriv.symm)
    have hend : e (s • v) = γ s := by
      change φ (s • v) = γ s
      simpa only [mul_one, hη1] using (heq 1 (by simp)).self_of_nhds.symm
    rw [hend]
    exact hmem ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩

end PoincareConjecture.RiemannianMetric
