import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RegularRadius

noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.CurvatureIntegral

theorem exists_greatest_punctured_radius
    {X : Type*} [MetricSpace X] (p : X) (P : X → Prop)
    {R : ℝ} (hR : 0 < R)
    (hsmall : ∃ s : ℝ, 0 < s ∧ ∀ y : X, 0 < dist p y → dist p y < s → P y) :
    ∃ b : ℝ, 0 < b ∧ 2 * b ≤ R ∧
      (∀ y : X, 0 < dist p y → dist p y < 2 * b → P y) ∧
      ∀ a : ℝ, 0 ≤ a → 2 * a ≤ R →
        (∀ y : X, 0 < dist p y → dist p y < 2 * a → P y) → a ≤ b := by
  let S : Set ℝ := {a | 0 ≤ a ∧ 2 * a ≤ R ∧
    ∀ y : X, 0 < dist p y → dist p y < 2 * a → P y}
  have hzero : 0 ∈ S := by
    refine ⟨le_rfl, by linarith, ?_⟩
    intro y hy hy'
    linarith
  have hbounded : BddAbove S := ⟨R / 2, fun a ha => by linarith [ha.2.1]⟩
  have hnonempty : S.Nonempty := ⟨0, hzero⟩
  have hpos : 0 < sSup S := by
    obtain ⟨s, hs, hp⟩ := hsmall
    have hr : 0 < min s R / 2 := half_pos (lt_min hs hR)
    apply hr.trans_le (le_csSup hbounded ?_)
    refine ⟨hr.le, by linarith [min_le_right s R], ?_⟩
    intro y hy hy'
    exact hp y hy (by linarith [min_le_left s R])
  refine ⟨sSup S, hpos, ?_, ?_, ?_⟩
  · have hsup : sSup S ≤ R / 2 := csSup_le hnonempty (fun a ha => by linarith [ha.2.1])
    linarith
  · intro y hy hy'
    obtain ⟨a, ha, hya⟩ := exists_lt_of_lt_csSup hnonempty
      (show dist p y / 2 < sSup S by linarith)
    exact ha.2.2 y hy (by linarith)
  · intro a ha haR hP
    exact le_csSup hbounded ⟨ha, haR, hP⟩

theorem exists_maximal_regular_radius_function
    {X : Type*} [MetricSpace X]
    (hX : Poincare.Alexandrov.CurvatureGEnegOne X)
    (hgeo : ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hpacking : ∀ α : ℝ, 0 < α → ∃ N : ℕ,
      Poincare.Alexandrov.ComparisonAnglePackingBound X α N)
    {c R : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hR : 0 < R) :
    ∃ b : X → ℝ, (∀ p, 0 < b p ∧ 2 * b p ≤ R) ∧
      (∀ p y : X, 0 < dist p y → dist p y < 2 * b p →
        ∀ s : ℝ, 0 < s → ∃ z : X,
          dist y z < s ∧ c * dist y z < dist p z - dist p y) ∧
      ∀ p : X, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ R →
        (∀ y : X, 0 < dist p y → dist p y < 2 * a →
          ∀ s : ℝ, 0 < s → ∃ z : X,
            dist y z < s ∧ c * dist y z < dist p z - dist p y) → a ≤ b p := by
  have hp (p : X) := exists_greatest_punctured_radius p
    (fun y => ∀ s : ℝ, 0 < s → ∃ z : X,
      dist y z < s ∧ c * dist y z < dist p z - dist p y) hR
    (Poincare.Alexandrov.exists_pos_punctured_distance_ascent
      hX hgeo hpacking hc0 hc1 p)
  choose b hb hcap hascent hmax using hp
  exact ⟨b, fun p => ⟨hb p, hcap p⟩, hascent, hmax⟩

theorem exists_maximal_regular_radius_finite_punctured_cover
    {X : Type*} [MetricSpace X]
    (hX : Poincare.Alexandrov.CurvatureGEnegOne X)
    (hgeo : ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hpacking : ∀ α : ℝ, 0 < α → ∃ N : ℕ,
      Poincare.Alexandrov.ComparisonAnglePackingBound X α N)
    {c R : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hR : 0 < R)
    {K : Set X} (hK : IsCompact K) :
    ∃ b : X → ℝ, ∃ F S : Finset X,
      (∀ p, 0 < b p ∧ 2 * b p ≤ R) ∧
      (∀ p y : X, 0 < dist p y → dist p y < 2 * b p →
        ∀ s : ℝ, 0 < s → ∃ z : X,
          dist y z < s ∧ c * dist y z < dist p z - dist p y) ∧
      (∀ p : X, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ R →
        (∀ y : X, 0 < dist p y → dist p y < 2 * a →
          ∀ s : ℝ, 0 < s → ∃ z : X,
            dist y z < s ∧ c * dist y z < dist p z - dist p y) → a ≤ b p) ∧
      (S : Set X) = {x | x ∈ K ∧ ∀ y, y ≠ x → b y ≤ dist y x} ∧
      K \ (S : Set X) ⊆ ⋃ y ∈ F, Metric.ball y (b y) \ {y} := by
  obtain ⟨b, hb, hascent, hmax⟩ :=
    exists_maximal_regular_radius_function hX hgeo hpacking hc0 hc1 hR
  obtain ⟨F, S, hS, hcover⟩ := exists_finite_punctured_ball_cover hK b (fun p => (hb p).1)
  exact ⟨b, F, S, hb, hascent, hmax, hS, hcover⟩

end Poincare.CurvatureIntegral
