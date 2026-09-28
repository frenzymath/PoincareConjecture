import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Distance
import Mathlib.Topology.Sequences









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology

namespace Poincare.GromovHausdorff

universe u


def VaryingRealizationSequence.comp
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    VaryingRealizationSequence (X ∘ φ) Y where
  ambient := S.ambient ∘ φ
  left := fun j => S.left (φ j)
  right := fun j => S.right (φ j)
  left_isometry := fun j => S.left_isometry (φ j)
  right_isometry := fun j => S.right_isometry (φ j)
  base_agree := fun j => S.base_agree (φ j)
  hausdorff_tendsto_zero := S.hausdorff_tendsto_zero.comp hφ

theorem VaryingRealizationSequence.PointConverges.comp
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    {S : VaryingRealizationSequence X Y} {p : ∀ j, (X j).carrier} {q : Y.carrier}
    (h : S.PointConverges p q) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    (S.comp φ hφ).PointConverges (fun j => p (φ j)) q := Filter.Tendsto.comp h hφ



theorem VaryingRealizationSequence.tendsto_dist_of_pointConverges
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    {p q : ∀ j, (X j).carrier} {x y : Y.carrier}
    (hp : S.PointConverges p x) (hq : S.PointConverges q y) :
    Tendsto (fun j => dist (p j) (q j)) atTop (𝓝 (dist x y)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
    (show Tendsto (fun j => dist (S.left j (p j)) (S.right j x) +
      dist (S.left j (q j)) (S.right j y)) atTop (𝓝 0) by
      simpa only [add_zero] using hp.add hq)
  rw [← (S.left_isometry j).dist_eq, ← (S.right_isometry j).dist_eq]
  exact dist_dist_dist_le _ _ _ _



theorem exists_approximating_maps_and_subseq_pointConverges
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (S : VaryingRealizationSequence
      (fun j => (X j).toBasedMetricSpaceBundle) Y.toBasedMetricSpaceBundle)
    {ρ σ : ℝ} (hρσ : ρ < σ) (hcompact : IsCompact (Metric.closedBall Y.base σ))
    (x : ∀ j, (X j).carrier) (hx : ∀ j, dist (X j).base (x j) ≤ ρ) :
    ∃ f : ∀ j, Y.carrier → (X j).carrier,
      (∀ q : Y.carrier, S.PointConverges (fun j => f j q) q) ∧
      ∃ y : Y.carrier, dist Y.base y ≤ ρ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun j => dist (S.left (φ j) (x (φ j))) (S.right (φ j) y))
          atTop (𝓝 0) := by
  classical
  let R : ∀ j, PointedGHRealization (X j) Y := fun j =>
    { ambient :=
        { carrier := (S.ambient j).carrier
          metric := (S.ambient j).metric
          base := S.left j (X j).base }
      left := S.left j
      right := S.right j
      left_isometry := S.left_isometry j
      right_isometry := S.right_isometry j
      left_base := rfl
      right_base := (S.base_agree j).symm }
  let e : ℕ → ℝ := fun j => pointedHausdorffDist (R j) + 1 / ((j : ℝ) + 1)
  have hR (j : ℕ) : pointedHausdorffDist (R j) < e j := by
    dsimp only [e]
    exact lt_add_of_pos_right _ (by positivity)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, R, pointedHausdorffDist, add_zero] using
      S.hausdorff_tendsto_zero.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose f hf using fun j q =>
    exists_left_point_lt_of_pointedHausdorffDist_lt (R j) (hR j) q
  have hfconv (q : Y.carrier) : S.PointConverges (fun j => f j q) q := by
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hf j q).le) he
  choose near hnear using fun j =>
    exists_right_point_lt_of_pointedHausdorffDist_lt (R j) (hR j) (x j)
  have hrad (j : ℕ) : dist Y.base (near j) ≤ ρ + e j := by
    have h := abs_dist_base_sub_dist_base_lt_of_corresponding (R j) (x j) (near j)
      (hnear j)
    have hlower := (abs_lt.mp h).1
    linarith [hx j]
  have hmem : ∀ᶠ j in atTop, near j ∈ Metric.closedBall Y.base σ := by
    filter_upwards [he.eventually_lt_const (sub_pos.mpr hρσ)] with j hj
    rw [Metric.mem_closedBall, dist_comm]
    linarith [hrad j]
  obtain ⟨y, _, φ, hφ, hy⟩ := hcompact.tendsto_subseq' hmem.frequently
  have hnearzero : Tendsto
      (fun j => dist (S.left (φ j) (x (φ j))) (S.right (φ j) (near (φ j))))
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun j => (hnear (φ j)).le)
      (he.comp hφ.tendsto_atTop)
  have hydist : Tendsto (fun j => dist (near (φ j)) y) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using tendsto_iff_dist_tendsto_zero.mp hy
  have hpoint : Tendsto
      (fun j => dist (S.left (φ j) (x (φ j))) (S.right (φ j) y)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (show Tendsto (fun j =>
        dist (S.left (φ j) (x (φ j))) (S.right (φ j) (near (φ j))) +
          dist (near (φ j)) y) atTop (𝓝 0) by
        simpa only [add_zero] using hnearzero.add hydist)
    calc
      dist (S.left (φ j) (x (φ j))) (S.right (φ j) y) ≤
          dist (S.left (φ j) (x (φ j))) (S.right (φ j) (near (φ j))) +
            dist (S.right (φ j) (near (φ j))) (S.right (φ j) y) := dist_triangle _ _ _
      _ = _ := by rw [(S.right_isometry (φ j)).dist_eq]
  have hyrad : dist Y.base y ≤ ρ := by
    apply le_of_tendsto_of_tendsto
      (show Tendsto (fun j => dist Y.base (near (φ j))) atTop (𝓝 (dist Y.base y)) from
        tendsto_const_nhds.dist hy)
      (show Tendsto (fun j => ρ + e (φ j)) atTop (𝓝 ρ) by
        simpa only [add_zero, Function.comp_def] using
          (he.comp hφ.tendsto_atTop).const_add ρ)
    exact Eventually.of_forall (fun j => hrad (φ j))
  exact ⟨f, hfconv, y, hyrad, φ, hφ, hpoint⟩

end Poincare.GromovHausdorff
