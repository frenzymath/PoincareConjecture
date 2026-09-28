import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RadiusLimitAscent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff

universe u

namespace Poincare.CurvatureIntegral

theorem eq_base_of_pointConverges_badAscentRadius_zero_at_scaled_spire
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    {κ L ρ b cap c c' : ℝ} (hκ : 0 < κ)
    (hL : 0 < L) (hρ : 0 < ρ) (hρb : ρ < κ * b / 2)
    (hbcap : b ≤ cap) (hroom : ρ + b < L)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel (X j) (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel (X j) (L + δ j) (hpos j)).carrier)
    (u0 : (ballModel Y L hL).carrier) (hu : S.PointConverges u u0)
    (hbound : ∀ j, dist (X j).base (u j).val ≤ ρ)
    (hc : 0 ≤ c) (hcc' : c' < c) (B : Y.carrier → ℝ)
    (hmax : ∀ p : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : Y.carrier, 0 < dist p y → dist p y < 2 * a →
        HasLocalDistanceAscent c' p y) → a ≤ B p)
    (hspire : ∀ y : Y.carrier, y ≠ Y.base → κ * B y ≤ dist y Y.base)
    (ha : Tendsto (fun j => badAscentRadius c b (u j).val) atTop (𝓝 0)) :
    u0.val = Y.base := by
  have hb : 0 < b := pos_of_mul_pos_right (by linarith only [hρ, hρb] : 0 < κ * b) hκ.le
  have hlimitBound : dist Y.base u0.val ≤ ρ :=
    le_of_tendsto (S.tendsto_dist_base u u0 hu) (Eventually.of_forall hbound)
  have hascent := local_distance_ascent_of_tendsto_badAscentRadius_zero
    hL δ hδ hpos S u u0 hu hc hcc'
    (show dist Y.base u0.val + b < L by linarith only [hlimitBound, hroom]) ha
  have hhalf : b / 2 ≤ B u0.val := by
    apply hmax u0.val (b / 2) (by linarith only [hb])
      (by linarith only [hbcap])
    intro y hy hyb
    exact hascent y hy (by linarith only [hyb])
  by_contra hne
  have hspireBound := hspire u0.val hne
  rw [dist_comm] at hspireBound
  have hscaled := mul_le_mul_of_nonneg_left hhalf hκ.le
  linarith only [hscaled, hspireBound, hlimitBound, hρb]

theorem tendsto_dist_base_zero_of_badAscentRadius_zero_at_scaled_spire
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    {κ L ρ b cap c c' : ℝ} (hκ : 0 < κ)
    (hL : 0 < L) (hρ : 0 < ρ) (hρb : ρ < κ * b / 2)
    (hbcap : b ≤ cap) (hroom : ρ + b < L)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel (X j) (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel (X j) (L + δ j) (hpos j)).carrier)
    (hbound : ∀ j, dist (X j).base (u j).val ≤ ρ)
    (hc : 0 ≤ c) (hcc' : c' < c) (B : Y.carrier → ℝ)
    (hmax : ∀ p : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : Y.carrier, 0 < dist p y → dist p y < 2 * a →
        HasLocalDistanceAscent c' p y) → a ≤ B p)
    (hspire : ∀ y : Y.carrier, y ≠ Y.base → κ * B y ≤ dist y Y.base)
    (ha : Tendsto (fun j => badAscentRadius c b (u j).val) atTop (𝓝 0)) :
    Tendsto (fun j => dist (X j).base (u j).val) atTop (𝓝 0) := by
  have hb : 0 < b := pos_of_mul_pos_right (by linarith only [hρ, hρb] : 0 < κ * b) hκ.le
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hnot
  have hnot' : ¬ ∀ᶠ j in atTop, dist (X j).base (u j).val < ε := by
    intro hevent
    apply hnot
    filter_upwards [hevent] with j hj
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hj
  obtain ⟨φ, hφ, hφbad⟩ := Filter.extraction_of_frequently_atTop
    (Filter.not_eventually.mp hnot')
  let C : FiniteDiameterBasedMetricSpace.{u} := ballModel Y L hL
  let σ := (ρ + L) / 2
  have hρL : ρ < L := by linarith only [hb, hroom]
  have hρσ : ρ < σ := by dsimp [σ]; linarith only [hρL]
  have hσL : σ < L := by dsimp [σ]; linarith only [hρL]
  have hcompact : IsCompact (Metric.closedBall C.base σ) :=
    isCompact_closedBall_ballModel Y hL C.base
      (by change dist Y.base Y.base + σ < L; simpa only [dist_self, zero_add] using hσL)
  let Sφ := S.comp φ hφ.tendsto_atTop
  obtain ⟨_, _, u0, _, ψ, hψ, hu0⟩ :=
    exists_approximating_maps_and_subseq_pointConverges Sφ hρσ hcompact
      (fun j => u (φ j)) (fun j => hbound (φ j))
  let S' := Sφ.comp ψ hψ.tendsto_atTop
  have hcofinal : Tendsto (fun j => φ (ψ j)) atTop atTop :=
    hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have heq : u0.val = Y.base :=
    eq_base_of_pointConverges_badAscentRadius_zero_at_scaled_spire
      hκ hL hρ hρb hbcap hroom (fun j => δ (φ (ψ j))) (hδ.comp hcofinal)
      (fun j => hpos (φ (ψ j))) S' (fun j => u (φ (ψ j))) u0 hu0
      (fun j => hbound (φ (ψ j))) hc hcc' B hmax hspire (ha.comp hcofinal)
  have hrad : Tendsto (fun j => dist (X (φ (ψ j))).base (u (φ (ψ j))).val)
      atTop (𝓝 0) := by
    have h := S'.tendsto_dist_base (fun j => u (φ (ψ j))) u0 hu0
    change Tendsto (fun j => dist (X (φ (ψ j))).base (u (φ (ψ j))).val)
      atTop (𝓝 (dist Y.base u0.val)) at h
    simpa only [heq, dist_self] using h
  have hεle : ε ≤ (0 : ℝ) := ge_of_tendsto hrad
    (Eventually.of_forall (fun j => le_of_not_gt (hφbad (ψ j))))
  exact (not_le_of_gt hε) hεle

theorem eq_base_of_pointConverges_badAscentRadius_zero_at_spire
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    {L ρ b cap c c' : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hρb : ρ < b / 2)
    (hbcap : b ≤ cap) (hroom : ρ + b < L)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel (X j) (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel (X j) (L + δ j) (hpos j)).carrier)
    (u0 : (ballModel Y L hL).carrier) (hu : S.PointConverges u u0)
    (hbound : ∀ j, dist (X j).base (u j).val ≤ ρ)
    (hc : 0 ≤ c) (hcc' : c' < c) (B : Y.carrier → ℝ)
    (hmax : ∀ p : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : Y.carrier, 0 < dist p y → dist p y < 2 * a →
        HasLocalDistanceAscent c' p y) → a ≤ B p)
    (hspire : ∀ y : Y.carrier, y ≠ Y.base → B y ≤ dist y Y.base)
    (ha : Tendsto (fun j => badAscentRadius c b (u j).val) atTop (𝓝 0)) :
    u0.val = Y.base := by
  exact eq_base_of_pointConverges_badAscentRadius_zero_at_scaled_spire (κ := 1)
    zero_lt_one hL hρ (by simpa only [one_mul] using hρb) hbcap hroom δ hδ hpos S u u0 hu hbound hc hcc' B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy) ha

theorem tendsto_dist_base_zero_of_badAscentRadius_zero_at_spire
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    {L ρ b cap c c' : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hρb : ρ < b / 2)
    (hbcap : b ≤ cap) (hroom : ρ + b < L)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel (X j) (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel (X j) (L + δ j) (hpos j)).carrier)
    (hbound : ∀ j, dist (X j).base (u j).val ≤ ρ)
    (hc : 0 ≤ c) (hcc' : c' < c) (B : Y.carrier → ℝ)
    (hmax : ∀ p : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : Y.carrier, 0 < dist p y → dist p y < 2 * a →
        HasLocalDistanceAscent c' p y) → a ≤ B p)
    (hspire : ∀ y : Y.carrier, y ≠ Y.base → B y ≤ dist y Y.base)
    (ha : Tendsto (fun j => badAscentRadius c b (u j).val) atTop (𝓝 0)) :
    Tendsto (fun j => dist (X j).base (u j).val) atTop (𝓝 0) := by
  exact tendsto_dist_base_zero_of_badAscentRadius_zero_at_scaled_spire (κ := 1)
    zero_lt_one hL hρ (by simpa only [one_mul] using hρb) hbcap hroom δ hδ hpos S u hbound hc hcc' B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy) ha

end Poincare.CurvatureIntegral
