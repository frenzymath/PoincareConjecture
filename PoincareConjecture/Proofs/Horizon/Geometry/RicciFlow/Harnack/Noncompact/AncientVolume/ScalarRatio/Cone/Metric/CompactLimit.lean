import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Compactness.Compact












noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {A B ι : Type*} [MetricSpace A] [MetricSpace B]



theorem tendstoUniformly_of_distortion_and_pointwise [CompactSpace A]
    {l : Filter ι} {f : ι → A → B} {e : A → B} (he : Isometry e)
    (hpoint : ∀ x, Tendsto (fun k => f k x) l (𝓝 (e x)))
    (hdist : TendstoUniformly (fun k => fun q : A × A => dist (f k q.1) (f k q.2))
      (fun q => dist q.1 q.2) l) : TendstoUniformly f e l := by
  rw [Metric.tendstoUniformly_iff] at hdist ⊢
  intro ε hε
  have hsmall : 0 < ε / 5 := by positivity
  obtain ⟨s, _, hs, hcover⟩ :=
    (isCompact_univ : IsCompact (univ : Set A)).finite_cover_balls hsmall
  have hnet : ∀ᶠ k in l, ∀ z ∈ s, dist (e z) (f k z) < ε / 5 := by
    apply hs.eventually_all.mpr
    intro z hz
    have h := (Metric.tendsto_nhds.mp (hpoint z)) (ε / 5) hsmall
    simpa only [dist_comm] using h
  filter_upwards [hnet, hdist (ε / 5) hsmall] with k hk hkd x
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  change dist x z < ε / 5 at hxz
  have hpair := hkd (z, x)
  rw [Real.dist_eq] at hpair
  have hupper : dist (f k z) (f k x) < dist z x + ε / 5 := by
    have hh := (abs_lt.mp hpair).1
    linarith
  calc
    dist (e x) (f k x) ≤ dist (e x) (e z) + dist (e z) (f k z) +
        dist (f k z) (f k x) := dist_triangle4 _ _ _ _
    _ < ε := by rw [he.dist_eq, dist_comm z x] at *; linarith [hk z hz]



theorem exists_isometric_ultrafilter_limit [CompactSpace B]
    (f : ℕ → A → B)
    (hdist : ∀ x y, Tendsto (fun k => dist (f k x) (f k y)) atTop (𝓝 (dist x y))) :
    ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
      ∃ e : A → B, Isometry e ∧ ∀ x, Tendsto (fun k => f k x) (U : Filter ℕ) (𝓝 (e x)) := by
  obtain ⟨e, _, he⟩ :=
    (isCompact_univ : IsCompact (univ : Set (A → B))).exists_mapClusterPt
      (f := atTop) (u := f) (by simp)
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp he
  have hpoint (x : A) : Tendsto (fun k => f k x) (U : Filter ℕ) (𝓝 (e x)) :=
    (continuous_apply x).continuousAt.tendsto.comp hlim
  refine ⟨U, hU, e, Isometry.of_dist_eq ?_, hpoint⟩
  intro x y
  exact tendsto_nhds_unique ((hpoint x).dist (hpoint y)) ((hdist x y).mono_left hU)



theorem mem_range_of_uniform_limit_and_approximation [CompactSpace A]
    {l : Filter ι} [l.NeBot] {f : ι → A → B} {e : A → B}
    (he : Continuous e) (hlim : TendstoUniformly f e l) {y : B}
    (hnear : ∀ ε > 0, ∀ᶠ k in l, ∃ x, dist (f k x) y < ε) : y ∈ range e := by
  have hclosed := (isCompact_range he).isClosed
  rw [← hclosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨k, hk, hx⟩ := ((Metric.tendstoUniformly_iff.mp hlim (ε / 2) hhalf).and
    (hnear (ε / 2) hhalf)).exists
  obtain ⟨x, hx⟩ := hx
  refine ⟨e x, mem_range_self x, ?_⟩
  calc
    dist y (e x) ≤ dist y (f k x) + dist (f k x) (e x) := dist_triangle _ _ _
    _ = dist (f k x) y + dist (e x) (f k x) := by congr 1 <;> exact dist_comm _ _
    _ < ε := by linarith [hk x]



theorem exists_isometric_limit_covering_approximated_points [CompactSpace A] [CompactSpace B]
    (f : ℕ → A → B)
    (hdist : TendstoUniformly (fun k => fun q : A × A => dist (f k q.1) (f k q.2))
      (fun q => dist q.1 q.2) atTop) :
    ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
      ∃ e : A → B, Isometry e ∧ TendstoUniformly f e (U : Filter ℕ) ∧
        ∀ y : B, (∀ ε > 0, ∀ᶠ k in atTop, ∃ x, dist (f k x) y < ε) → y ∈ range e := by
  obtain ⟨U, hU, e, he, hpoint⟩ := exists_isometric_ultrafilter_limit f
    (fun x y => hdist.tendsto_at (x, y))
  have hdistU : TendstoUniformly
      (fun k => fun q : A × A => dist (f k q.1) (f k q.2))
      (fun q => dist q.1 q.2) (U : Filter ℕ) := by
    rw [Metric.tendstoUniformly_iff] at hdist ⊢
    exact fun ε hε => hU (hdist ε hε)
  have hlim := tendstoUniformly_of_distortion_and_pointwise he hpoint hdistU
  refine ⟨U, hU, e, he, hlim, ?_⟩
  intro y hy
  exact mem_range_of_uniform_limit_and_approximation he.continuous hlim
    (fun ε hε => hU (hy ε hε))

end Poincare.AncientVolume.ScalarRatio
