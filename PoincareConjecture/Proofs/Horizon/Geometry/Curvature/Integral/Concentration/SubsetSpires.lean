import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.MaximalRadius

set_option autoImplicit false

open Set

namespace Poincare.CurvatureIntegral

theorem exists_finite_punctured_ball_cover_on_subset
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    (b : X → ℝ) (hb : ∀ x ∈ K, 0 < b x) :
    ∃ F S : Finset X, (F : Set X) ⊆ K ∧ (S : Set X) ⊆ K ∧
      (S : Set X) = {x | x ∈ K ∧ ∀ y ∈ K, y ≠ x → b y ≤ dist y x} ∧
      K \ (S : Set X) ⊆ ⋃ y ∈ F, Metric.ball y (b y) \ {y} := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨F, S, hS, hcover⟩ := exists_finite_punctured_ball_cover
    (isCompact_univ : IsCompact (univ : Set K))
    (fun x : K => b x) (fun x => hb x x.property)
  refine ⟨F.image Subtype.val, S.image Subtype.val, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hyS : y ∈ (S : Set K) := hy
      rw [hS] at hyS
      refine ⟨y.property, ?_⟩
      intro z hz hzy
      exact hyS.2 ⟨z, hz⟩ (fun h => hzy (congrArg Subtype.val h))
    · rintro ⟨hxK, hx⟩
      refine Finset.mem_image.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
      change (⟨x, hxK⟩ : K) ∈ (S : Set K)
      rw [hS]
      refine ⟨mem_univ _, ?_⟩
      intro y hy
      exact hx y y.property (fun h => hy (Subtype.ext h))
  · intro x hx
    have hxS : (⟨x, hx.1⟩ : K) ∉ (S : Set K) := by
      intro h
      exact hx.2 (Finset.mem_image.mpr ⟨⟨x, hx.1⟩, h, rfl⟩)
    obtain ⟨y, hy, hxy, hne⟩ := mem_iUnion₂.mp (hcover ⟨mem_univ _, hxS⟩)
    refine mem_iUnion₂.mpr ⟨y.val, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_, ?_⟩
    · exact hxy
    · intro h
      exact hne (Subtype.ext (mem_singleton_iff.mp h))

theorem exists_maximal_regular_radius_finite_punctured_cover_on_subset
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
      (F : Set X) ⊆ K ∧ (S : Set X) ⊆ K ∧
      (S : Set X) = {x | x ∈ K ∧ ∀ y ∈ K, y ≠ x → b y ≤ dist y x} ∧
      K \ (S : Set X) ⊆ ⋃ y ∈ F, Metric.ball y (b y) \ {y} := by
  obtain ⟨b, hb, hascent, hmax⟩ :=
    exists_maximal_regular_radius_function hX hgeo hpacking hc0 hc1 hR
  obtain ⟨F, S, hFK, hSK, hS, hcover⟩ :=
    exists_finite_punctured_ball_cover_on_subset hK b (fun x _ => (hb x).1)
  exact ⟨b, F, S, hb, hascent, hmax, hFK, hSK, hS, hcover⟩

end Poincare.CurvatureIntegral
