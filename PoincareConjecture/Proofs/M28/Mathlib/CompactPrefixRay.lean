import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set Filter
open scoped Topology




theorem exists_pointwise_metric_limit_of_eventually_compact
    {A X : Type*} [MetricSpace X]
    (S : Set A) (f : ℕ → A → X) (d : A → A → ℝ)
    (hcompact : ∀ x ∈ S, ∃ K : Set X, IsCompact K ∧
      ∀ᶠ n in atTop, f n x ∈ K)
    (hdist : ∀ x ∈ S, ∀ y ∈ S,
      Tendsto (fun n => dist (f n x) (f n y)) atTop (𝓝 (d x y))) :
    ∃ g : A → X,
      (∀ x ∈ S, Tendsto (fun n => f n x)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (g x))) ∧
      ∀ x ∈ S, ∀ y ∈ S, dist (g x) (g y) = d x y := by
  classical
  have hpoint (x : A) (hx : x ∈ S) :
      ∃ y : X, Tendsto (fun n => f n x)
        (hyperfilter ℕ : Filter ℕ) (𝓝 y) := by
    obtain ⟨K, hK, hf⟩ := hcompact x hx
    have hF : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n x ∈ K :=
      hf.filter_mono Nat.hyperfilter_le_atTop
    obtain ⟨y, _hyK, hy⟩ := hK.ultrafilter_le_nhds'
      ((hyperfilter ℕ).map fun n => f n x) hF
    rw [Ultrafilter.coe_map] at hy
    exact ⟨y, hy⟩
  let g : A → X := fun x =>
    if hx : x ∈ S then Classical.choose (hpoint x hx) else f 0 x
  have hg (x : A) (hx : x ∈ S) :
      Tendsto (fun n => f n x)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (g x)) := by
    simpa only [g, dif_pos hx] using Classical.choose_spec (hpoint x hx)
  refine ⟨g, hg, ?_⟩
  intro x hx y hy
  exact tendsto_nhds_unique ((hg x hx).dist (hg y hy))
    ((hdist x hx y hy).mono_left Nat.hyperfilter_le_atTop)




theorem exists_isometric_finite_ray_of_compact_prefixes
    {X : Type*} [MetricSpace X] {p : X} {a : ℝ}
    {arc : ℕ → ℝ → X} {length : ℕ → ℝ}
    (ha : 0 < a) (hlength : Tendsto length atTop (𝓝 a))
    (hanchor : ∀ᶠ n in atTop, arc n 0 = p)
    (hprefix : ∀ T : ℝ, 0 < T → T < a →
      ∃ K : Set X, IsCompact K ∧
        ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, arc n t ∈ K)
    (hdist : ∀ n, ∀ s ∈ Icc (0 : ℝ) (length n),
      ∀ t ∈ Icc (0 : ℝ) (length n),
        dist (arc n s) (arc n t) = |s - t|) :
    ∃ gamma : ℝ → X,
      gamma 0 = p ∧
      Isometry (fun t : Ico (0 : ℝ) a => gamma t.1) ∧
      (∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
        dist (gamma s) (gamma t) = |s - t|) ∧
      ∀ t ∈ Ico (0 : ℝ) a, Tendsto (fun n => arc n t)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (gamma t)) := by
  have hcompact (t : ℝ) (ht : t ∈ Ico (0 : ℝ) a) :
      ∃ K : Set X, IsCompact K ∧ ∀ᶠ n in atTop, arc n t ∈ K := by
    have hTpos : 0 < (t + a) / 2 := by linarith [ht.1]
    have hTlt : (t + a) / 2 < a := by linarith [ht.2]
    have htT : t ≤ (t + a) / 2 := by linarith [ht.2]
    obtain ⟨K, hK, hcapture⟩ := hprefix ((t + a) / 2) hTpos hTlt
    exact ⟨K, hK, hcapture.mono fun _ hn => hn t ⟨ht.1, htT⟩⟩
  have hpair (s : ℝ) (hs : s ∈ Ico (0 : ℝ) a)
      (t : ℝ) (ht : t ∈ Ico (0 : ℝ) a) :
      Tendsto (fun n => dist (arc n s) (arc n t)) atTop (𝓝 |s - t|) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_order.mp hlength).1 s hs.2,
      (tendsto_order.mp hlength).1 t ht.2] with n hsL htL
    exact (hdist n s ⟨hs.1, hsL.le⟩ t ⟨ht.1, htL.le⟩).symm
  obtain ⟨gamma, hgamma, hmetric⟩ :=
    exists_pointwise_metric_limit_of_eventually_compact
      (Ico (0 : ℝ) a) arc (fun s t => |s - t|) hcompact hpair
  have hsourceZero : Tendsto (fun n => arc n 0) atTop (𝓝 p) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hanchor] with n hn
    exact hn.symm
  refine ⟨gamma, ?_, ?_, hmetric, hgamma⟩
  · exact tendsto_nhds_unique (hgamma 0 ⟨le_rfl, ha⟩)
      (hsourceZero.mono_left Nat.hyperfilter_le_atTop)
  · apply Isometry.of_dist_eq
    intro s t
    change dist (gamma s.1) (gamma t.1) = dist s.1 t.1
    simpa only [Real.dist_eq] using hmetric s.1 s.2 t.1 t.2




theorem finite_ray_radius_eq_of_source_bounds
    {X : Type*} [MetricSpace X] {a : ℝ}
    {arc : ℕ → ℝ → X} {gamma : ℝ → X} {length defect : ℕ → ℝ}
    {r : X → ℝ} (hr : Continuous r)
    (hlength : Tendsto length atTop (𝓝 a))
    (hdefect : Tendsto defect atTop (𝓝 0))
    (hgamma : ∀ t ∈ Ico (0 : ℝ) a, Tendsto (fun n => arc n t)
      (hyperfilter ℕ : Filter ℕ) (𝓝 (gamma t)))
    (hbound : ∀ t ∈ Ico (0 : ℝ) a, ∀ᶠ n in atTop,
      a - t ≤ r (arc n t) ∧ r (arc n t) ≤ length n - t + defect n) :
    ∀ t ∈ Ico (0 : ℝ) a, r (gamma t) = a - t := by
  intro t ht
  have hupper : Tendsto (fun n => length n - t + defect n)
      atTop (𝓝 (a - t)) := by
    simpa only [add_zero] using (hlength.sub tendsto_const_nhds).add hdefect
  have hradius : Tendsto (fun n => r (arc n t)) atTop (𝓝 (a - t)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      ((hbound t ht).mono fun _ hn => hn.1)
      ((hbound t ht).mono fun _ hn => hn.2)
  exact tendsto_nhds_unique ((hr.tendsto (gamma t)).comp (hgamma t ht))
    (hradius.mono_left Nat.hyperfilter_le_atTop)
