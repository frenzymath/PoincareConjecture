import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.CompactLimit

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

theorem exists_common_isometric_limits_preserving_cross_distances
    {ι : Type*} {A : ι → Type*} [∀ i, MetricSpace (A i)] [∀ i, CompactSpace (A i)]
    {B : Type*} [MetricSpace B] [CompactSpace B]
    (f : ℕ → ∀ i, A i → B) (D : ∀ i j, A i → A j → ℝ)
    (hdiag : ∀ i, TendstoUniformly
      (fun k (z : A i × A i) => dist (f k i z.1) (f k i z.2))
      (fun z => dist z.1 z.2) atTop)
    (hcross : ∀ i j x y, Tendsto (fun k => dist (f k i x) (f k j y))
      atTop (𝓝 (D i j x y))) :
    ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧ ∃ e : ∀ i, A i → B,
      (∀ i, Isometry (e i)) ∧
      (∀ i, TendstoUniformly (fun k => f k i) (e i) (U : Filter ℕ)) ∧
      (∀ i j x y, dist (e i x) (e j y) = D i j x y) ∧
      ∀ i y, (∀ ε > 0, ∀ᶠ k in atTop, ∃ x, dist (f k i x) y < ε) → y ∈ range (e i) := by
  obtain ⟨e, _, he⟩ :=
    (isCompact_univ : IsCompact (univ : Set (∀ i, A i → B))).exists_mapClusterPt
      (f := atTop) (u := f) (by simp)
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp he
  have hpoint (i : ι) (x : A i) :
      Tendsto (fun k => f k i x) (U : Filter ℕ) (𝓝 (e i x)) :=
    (continuous_apply x).continuousAt.tendsto.comp
      ((continuous_apply i).continuousAt.tendsto.comp hlim)
  have hisom (i : ι) : Isometry (e i) := by
    apply Isometry.of_dist_eq
    intro x y
    exact tendsto_nhds_unique ((hpoint i x).dist (hpoint i y))
      (((hdiag i).tendsto_at (x, y)).mono_left hU)
  have huniform (i : ι) : TendstoUniformly (fun k => f k i) (e i) (U : Filter ℕ) := by
    apply tendstoUniformly_of_distortion_and_pointwise (hisom i) (hpoint i)
    rw [Metric.tendstoUniformly_iff]
    exact fun ε hε => hU (Metric.tendstoUniformly_iff.mp (hdiag i) ε hε)
  refine ⟨U, hU, e, hisom, huniform, ?_, ?_⟩
  · intro i j x y
    exact tendsto_nhds_unique ((hpoint i x).dist (hpoint j y)) ((hcross i j x y).mono_left hU)
  · intro i y hy
    exact mem_range_of_uniform_limit_and_approximation (hisom i).continuous (huniform i)
      (fun ε hε => hU (hy ε hε))

end Poincare.AncientVolume.ScalarRatio
