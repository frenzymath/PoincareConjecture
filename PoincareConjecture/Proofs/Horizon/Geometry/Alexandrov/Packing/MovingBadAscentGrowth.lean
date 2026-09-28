import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.BadAscentGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.LocalRank
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.MovingConfigurations

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Poincare.GromovHausdorff

universe u

namespace Poincare.Alexandrov

theorem hasSmallAngleConfiguration_of_moving_bad_ascent_blowup
    {X Z : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
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
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j)
    (ht0 : Tendsto t atTop (𝓝 0))
    (F : ∀ j, (X j).carrier → (Z j).carrier)
    (hFcenter : ∀ j, F j (X j).base = (u j).val)
    (hscale : ∀ j (x y : (X j).carrier),
      dist x y = t j * dist (F j x) (F j y))
    {k : ℕ} (q : ∀ j, Fin k → (X j).carrier)
    (b : Fin k → ℝ) (d : Fin k → Fin k → ℝ)
    (hb : ∀ i, 0 < b i)
    (hqb : ∀ i, Tendsto (fun j => dist (X j).base (q j i)) atTop (𝓝 (b i)))
    (hqd : ∀ i l, Tendsto (fun j => dist (q j i) (q j l)) atTop (𝓝 (d i l)))
    {θ c ε : ℝ} (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ)) (hε : 0 < ε)
    (hangle : ∀ i l : Fin k, i ≠ l → θ < comparisonAngle (b i) (b l) (d i l))
    (y : ∀ j, (X j).carrier)
    (hy0 : Tendsto (fun j => dist (X j).base (y j)) atTop (𝓝 0))
    (hyfar : ∀ᶠ j in atTop, ε * t j ≤ dist (X j).base (y j))
    (hybad : ∀ᶠ j in atTop,
      ¬ (∀ s : ℝ, 0 < s → ∃ z : (X j).carrier,
        dist (y j) z < s ∧
          c * dist (y j) z < dist (X j).base z - dist (X j).base (y j))) :
    HasSmallAngleConfiguration θ u₀.val (k + 1) := by
  classical
  obtain ⟨β, hθβ, hβpi, hspheres⟩ :=
    exists_eventually_scaled_angle_configuration_of_bad_ascent hX hgeo t ht ht0
      q b d hb hqb hqd hθ hθpi hc hcθ hε hangle y hy0 hyfar hybad
  obtain ⟨R₀, hR₀, hconfig⟩ :=
    exists_pos_radius_for_scaled_moving_configurations hθ hθβ
      (hβpi.trans (by linarith [Real.pi_pos]))
  let a : ℝ := dist Y.base u₀.val
  have haL : a < L := by
    have h := u₀.property
    change dist u₀.val Y.base < L at h
    simpa only [a, dist_comm] using h
  let gap : ℝ := L - a
  have hgap : 0 < gap := sub_pos.mpr haL
  let ρc : ℝ := a + gap / 4
  let σ : ℝ := a + 3 * gap / 4
  have haρc : a < ρc := by dsimp [ρc]; linarith
  have hσL : σ < L := by dsimp [σ, gap]; linarith
  have hcenter : Tendsto (fun j => dist (Z j).base (u j).val) atTop (𝓝 a) :=
    S.tendsto_dist_base u u₀ hu
  have hbounded : ∀ᶠ j in atTop, dist (Z j).base (u j).val ≤ ρc :=
    (hcenter.eventually_lt_const haρc).mono (fun _ h => h.le)
  intro ρ hρ
  let R := min ρ (min ε (min R₀ (gap / 8))) / 2
  have hR : 0 < R := half_pos (lt_min hρ (lt_min hε (lt_min hR₀ (by positivity))))
  have hRρ : R < ρ := by
    dsimp [R]
    linarith [min_le_left ρ (min ε (min R₀ (gap / 8)))]
  have hRε : R < ε := by
    dsimp [R]
    linarith [min_le_right ρ (min ε (min R₀ (gap / 8))), min_le_left ε (min R₀ (gap / 8))]
  have hRR₀ : R < R₀ := by
    dsimp [R]
    linarith [min_le_right ρ (min ε (min R₀ (gap / 8))),
      min_le_right ε (min R₀ (gap / 8)), min_le_left R₀ (gap / 8)]
  have hRgap : R < gap / 8 := by
    dsimp [R]
    linarith [min_le_right ρ (min ε (min R₀ (gap / 8))),
      min_le_right ε (min R₀ (gap / 8)), min_le_right R₀ (gap / 8)]
  have hroom : ρc + R < σ := by dsimp [ρc, σ]; linarith
  have hsource : ∀ᶠ j in atTop, ρc + R < L + δ j := by
    have hlim : Tendsto (fun j => L + δ j) atTop (𝓝 L) := by
      simpa only [add_zero] using hδ.const_add L
    exact hlim.eventually_const_lt (hroom.trans hσL)
  obtain ⟨φ, hφ, hφgood⟩ := Filter.extraction_of_frequently_atTop
    (((hspheres R hR hRε).and (hbounded.and hsource)).frequently)
  choose w hw hwsep using fun j => (hφgood j).1
  let A : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
    ballModel (Z j) (L + δ j) (hpos j)
  let B : FiniteDiameterBasedMetricSpace.{u} := ballModel Y L hL
  have hscaledrad (j : ℕ) (i : Fin (k + 1)) :
      dist (u (φ j)).val (F (φ j) (w j i)) = R := by
    apply (mul_left_cancel₀ (ht (φ j)).ne')
    rw [← hFcenter (φ j), ← hscale]
    exact hw j i
  have himagebound (j : ℕ) (i : Fin (k + 1)) :
      dist (Z (φ j)).base (F (φ j) (w j i)) ≤ ρc + R := by
    calc
      dist (Z (φ j)).base (F (φ j) (w j i)) ≤
          dist (Z (φ j)).base (u (φ j)).val +
            dist (u (φ j)).val (F (φ j) (w j i)) := dist_triangle _ _ _
      _ ≤ ρc + R := by rw [hscaledrad]; exact add_le_add (hφgood j).2.1 le_rfl
  let x : ∀ j, Fin (k + 1) → (A (φ j)).carrier := fun j i =>
    ⟨F (φ j) (w j i), by
      change dist (F (φ j) (w j i)) (Z (φ j)).base < L + δ (φ j)
      rw [dist_comm]
      exact (himagebound j i).trans_lt (hφgood j).2.2⟩
  have hx (j : ℕ) (i : Fin (k + 1)) : dist (u (φ j)) (x j i) = R :=
    hscaledrad j i
  have hcompact : IsCompact (Metric.closedBall B.base σ) := by
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' Metric.closedBall B.base σ = Metric.closedBall Y.base σ := by
      ext z
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hz
        have hzL : z ∈ Metric.ball Y.base L := by
          change dist z Y.base < L
          exact (show dist z Y.base ≤ σ from hz).trans_lt hσL
        exact ⟨⟨z, hzL⟩, hz, rfl⟩
    rw [heq]
    exact isCompact_closedBall Y.base σ
  have hseparated : ∀ᶠ j in atTop, ∀ i l : Fin (k + 1), i ≠ l →
      β ≤ comparisonAngle (t (φ j) * dist (u (φ j)) (x j i))
        (t (φ j) * dist (u (φ j)) (x j l)) (t (φ j) * dist (x j i) (x j l)) := by
    apply Eventually.of_forall
    intro j i l hil
    change β ≤ comparisonAngle (t (φ j) * dist (u (φ j)).val (F (φ j) (w j i)))
      (t (φ j) * dist (u (φ j)).val (F (φ j) (w j l)))
      (t (φ j) * dist (F (φ j) (w j i)) (F (φ j) (w j l)))
    rw [← hFcenter (φ j), ← hscale, ← hscale, ← hscale]
    exact (hwsep j i l hil).le
  obtain ⟨z, hz, hzsep⟩ := hconfig (S.comp φ hφ.tendsto_atTop)
    (hu.comp φ hφ.tendsto_atTop) hR hRR₀ hroom hcompact
    (Eventually.of_forall (fun j => (hφgood j).2.1)) x hx (fun j => t (φ j))
    (ht0.comp hφ.tendsto_atTop) (Eventually.of_forall (fun j => (ht (φ j)).ne')) hseparated
  exact ⟨R, hR, hRρ, fun i => (z i).val, hz, hzsep⟩

end Poincare.Alexandrov
