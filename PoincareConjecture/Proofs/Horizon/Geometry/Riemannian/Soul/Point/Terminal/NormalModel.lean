import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.ZeroRank
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ExponentialRays














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_radial_normal_chart (g : RiemannianMetric n M) (q : M) :
    ∃ (r : ℝ) (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M),
      0 < r ∧ e.source = Metric.ball 0 r ∧ e 0 = q ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      HasFDerivAt (fun v => extChartAt (𝓡 n) q (e v))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 ∧
      ∀ v ∈ Metric.ball 0 r,
        g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 r} := by
  obtain ⟨φ, hφ0, hφq, hφ, hφi, hφd, Γ, _, hΓ⟩ := g.exists_exponential_chart q
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (φ.open_source.mem_nhds hφ0)
  let e := φ.restrOpen (Metric.ball 0 r) isOpen_ball
  have hsource : e.source = Metric.ball 0 r := inter_eq_right.mpr hball
  have hexp : ∀ v ∈ Metric.ball 0 r, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = q ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) q (γ t))
        ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) v) 0 ∧
      γ 1 = e v := by
    intro v hv
    have hvΓ := hΓ v (hball hv)
    obtain ⟨hgeo, h0, hd⟩ := g.geodesic_of_coordinate_exponential q
      (fun t => Γ (v, t)) v hvΓ.1
      (fun t ht => ⟨(hvΓ.2.2.2 t ht).1, (hvΓ.2.2.2 t ht).2.1⟩)
    refine ⟨1 / 2, by norm_num, fun t => (extChartAt (𝓡 n) q).symm (Γ (v, t)).1,
      ?_, h0, hd, hvΓ.2.1⟩
    intro t ht
    exact hgeo t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨r, e, hr, hsource, hφq, hφ.mono inter_subset_left,
    hφi.mono inter_subset_left, hφd, ?_⟩
  intro v hv
  exact isGeodesicOn_radial_of_initial_data q
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) e hexp hv

omit [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] in
theorem finrank_lt_of_normal_disk_subset_empty_interior
    {S : Set M} (hinterior : interior S = ∅)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball 0 r ⊆ e.source)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hdisk : e '' (Metric.ball 0 r ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) ⊆ S) :
    Module.finrank ℝ V < n := by
  have hproper : V ≠ ⊤ := by
    intro htop
    have hsub : e '' Metric.ball 0 r ⊆ S := by
      simpa only [htop, Submodule.top_coe, inter_univ] using hdisk
    have hz : e 0 ∈ interior S :=
      interior_maximal hsub (e.isOpen_image_of_subset_source isOpen_ball hball)
        ⟨0, mem_ball_self hr, rfl⟩
    simp only [hinterior, notMem_empty] at hz
  simpa using Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)

theorem exists_normal_model_or_positive_span [ConnectedSpace M]
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ), g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {q : M} (hq : q ∈ S) :
    ∃ (r : ℝ) (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M),
      0 < r ∧ e.source = Metric.ball 0 r ∧ e 0 = q ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      HasFDerivAt (fun v => extChartAt (𝓡 n) q (e v))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 ∧
      (∀ v ∈ Metric.ball 0 r,
        g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 r}) ∧
      (∀ v ∈ Metric.ball 0 r, e v ∈ S → ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ S) ∧
      (S = {q} ∨ 0 < Module.finrank ℝ (Submodule.span ℝ (Metric.ball 0 r ∩ e ⁻¹' S))) := by
  obtain ⟨r, e, hr, hs, he0, he, hei, hed, hgeo⟩ := g.exists_radial_normal_chart q
  refine ⟨r, e, hr, hs, he0, he, hei, hed, hgeo, ?_, ?_⟩
  · intro v hv hend t ht
    have hscaled {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : u • v ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      rw [norm_smul, Real.norm_of_nonneg hu.1]
      exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg v)).trans_lt
        (by simpa only [one_mul] using hv)
    exact hconv (fun u : ℝ => e (u • v)) 0 1
      (fun u hu => hgeo v hv u (hscaled hu))
      (by simpa only [zero_smul, he0] using hq)
      (by simpa only [one_smul] using hend) ht
  · by_cases hspan : Submodule.span ℝ (Metric.ball 0 r ∩ e ⁻¹' S) = ⊥
    · exact Or.inl (g.eq_singleton_of_zero_local_span_of_every_geodesic hcomplete
        hconv hq e he0 hr (hs ▸ Subset.rfl) hspan)
    · exact Or.inr (Nat.pos_of_ne_zero (fun hz => hspan (Submodule.finrank_eq_zero.mp hz)))

end PoincareConjecture.RiemannianMetric
