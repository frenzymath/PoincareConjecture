import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.MovingBadAscentGrowth

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Poincare.GromovHausdorff

universe u

namespace Poincare.Alexandrov

theorem hasSmallAngleConfiguration_succ_of_old_limit
    {X Z : ℕ → BasedMetricSpaceBundle.{u}}
    {V Y : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    {A : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {L₀ : ℝ} (hL₀ : 0 < L₀)
    (S₀ : VaryingRealizationSequence (fun j => (A j).toBasedMetricSpaceBundle)
      (ballModel V L₀ hL₀).toBasedMetricSpaceBundle)
    (e : ∀ j, (A j).carrier → (X j).carrier) (he : ∀ j, Isometry (e j))
    (v : ∀ j, (A j).carrier) (v₀ : (ballModel V L₀ hL₀).carrier)
    (hv : S₀.PointConverges v v₀) (hecenter : ∀ j, e j (v j) = (X j).base)
    {L : ℝ} (hL : 0 < L) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel (Z j) (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel (Z j) (L + δ j) (hpos j)).carrier)
    (u₀ : (ballModel Y L hL).carrier) (hu : S.PointConverges u u₀)
    (hX : ∀ j, CurvatureGEnegOne (X j).carrier)
    (hgeo : ∀ j, ∀ x y : (X j).carrier,
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j) (ht0 : Tendsto t atTop (𝓝 0))
    (F : ∀ j, (X j).carrier → (Z j).carrier)
    (hFcenter : ∀ j, F j (X j).base = (u j).val)
    (hscale : ∀ j (x y : (X j).carrier),
      dist x y = t j * dist (F j x) (F j y))
    {k : ℕ} {θ c ε : ℝ} (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ)) (hε : 0 < ε)
    (hold : HasSmallAngleConfiguration θ v₀.val k)
    (y : ∀ j, (X j).carrier)
    (hy0 : Tendsto (fun j => dist (X j).base (y j)) atTop (𝓝 0))
    (hyfar : ∀ᶠ j in atTop, ε * t j ≤ dist (X j).base (y j))
    (hybad : ∀ᶠ j in atTop,
      ¬ (∀ s : ℝ, 0 < s → ∃ z : (X j).carrier,
        dist (y j) z < s ∧
          c * dist (y j) z < dist (X j).base z - dist (X j).base (y j))) :
    HasSmallAngleConfiguration θ u₀.val (k + 1) := by
  classical
  let B₀ : FiniteDiameterBasedMetricSpace.{u} := ballModel V L₀ hL₀
  have hvinside : dist V.base v₀.val < L₀ := by
    have h := v₀.property
    change dist v₀.val V.base < L₀ at h
    simpa only [dist_comm] using h
  obtain ⟨r, hr, hrgap, w, hw, hwangle⟩ := hold (L₀ - dist V.base v₀.val)
    (sub_pos.mpr hvinside)
  have hwinside (i : Fin k) : w i ∈ Metric.ball V.base L₀ := by
    change dist (w i) V.base < L₀
    rw [dist_comm]
    calc
      dist V.base (w i) ≤ dist V.base v₀.val + dist v₀.val (w i) :=
        dist_triangle _ _ _
      _ = dist V.base v₀.val + r := by rw [hw]
      _ < L₀ := by linarith
  let w₀ : Fin k → B₀.carrier := fun i => ⟨w i, hwinside i⟩
  have hcompact : IsCompact (Metric.closedBall B₀.base (L₀ / 2)) := by
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' Metric.closedBall B₀.base (L₀ / 2) =
        Metric.closedBall V.base (L₀ / 2) := by
      ext z
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hz
        have hzL : z ∈ Metric.ball V.base L₀ := by
          change dist z V.base < L₀
          exact (show dist z V.base ≤ L₀ / 2 from hz).trans_lt (half_lt_self hL₀)
        exact ⟨⟨z, hzL⟩, hz, rfl⟩
    rw [heq]
    exact isCompact_closedBall V.base (L₀ / 2)
  obtain ⟨f, hf, _⟩ := exists_approximating_maps_and_subseq_pointConverges
    S₀ (ρ := 0) (σ := L₀ / 2) (half_pos hL₀) hcompact
    (fun j => (A j).base) (fun j => by simp)
  let q : ∀ j, Fin k → (X j).carrier := fun j i => e j (f j (w₀ i))
  have hqb (i : Fin k) :
      Tendsto (fun j => dist (X j).base (q j i)) atTop (𝓝 r) := by
    have hsource : (fun j => dist (X j).base (q j i)) =
        (fun j => dist (v j) (f j (w₀ i))) := by
      funext j
      change dist (X j).base (e j (f j (w₀ i))) = dist (v j) (f j (w₀ i))
      rw [← hecenter j]
      exact (he j).dist_eq _ _
    rw [hsource, ← (show dist v₀ (w₀ i) = r from hw i)]
    exact S₀.tendsto_dist_of_pointConverges hv (hf (w₀ i))
  have hqd (i l : Fin k) : Tendsto (fun j => dist (q j i) (q j l)) atTop
      (𝓝 (dist (w i) (w l))) := by
    have hsource : (fun j => dist (q j i) (q j l)) =
        (fun j => dist (f j (w₀ i)) (f j (w₀ l))) := by
      funext j
      exact (he j).dist_eq _ _
    rw [hsource]
    exact S₀.tendsto_dist_of_pointConverges (hf (w₀ i)) (hf (w₀ l))
  apply hasSmallAngleConfiguration_of_moving_bad_ascent_blowup hL δ hδ hpos S u u₀ hu
    hX hgeo t ht ht0 F hFcenter hscale q (fun _ => r) (fun i l => dist (w i) (w l))
    (fun _ => hr) hqb hqd hθ hθpi hc hcθ hε ?_ y hy0 hyfar hybad
  intro i l hil
  simpa only [hw i, hw l] using hwangle i l hil

theorem HasSmallAngleConfiguration.lt_localAnglePackingRank_of_succ
    {Y : Type*} [MetricSpace Y] {θ : ℝ} {p : Y} {k N : ℕ}
    (h : HasSmallAngleConfiguration θ p (k + 1))
    (hpack : ComparisonAnglePackingBound Y θ N) :
    k < localAnglePackingRank θ p := by
  exact Nat.lt_of_succ_le ((localAnglePackingRank_spec hpack p).2.2 (k + 1) |>.mp h)

end Poincare.Alexandrov
