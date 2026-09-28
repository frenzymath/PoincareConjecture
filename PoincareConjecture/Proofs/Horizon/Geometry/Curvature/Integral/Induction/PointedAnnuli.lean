import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.LimitSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SlabNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.GeometricParameters











noncomputable section
set_option autoImplicit false

open Set Filter Topology
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

theorem exists_eventually_annular_induction_geometry_at_small_radii
    {m : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) (M j)]
    [∀ j, IsManifold (𝓡 (m + 2)) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric (m + 2) (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 (m + 2)) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ a b α : ℝ, 0 < a ∧ a < b ∧ 3 * b / 2 ≤ 1 ∧ 0 < α ∧
      ∀ᶠ j in atTop, ∃ (f : M j → ℝ) (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
        (I : Set ℝ), IsOpen I ∧ IsProperMap (I.restrictPreimage f) ∧
        Icc a (3 * b / 2) ⊆ I ∧
        (∀ x : M j, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ t ∈ Icc a (3 * b / 2), (g j).regularLevelArea hf t ≤ α * t ^ (m + 1)) ∧
        (∀ t ∈ Icc a (3 * b / 2), ∀ x, f x = t →
          ∀ v : TangentSpace (𝓡 (m + 2)) x,
            (g j).inner x ((D j).gradient f x) v = 0 →
            (D j).hessian f x v v / Real.sqrt ((D j).levelQ f x) ≤
              (α / t) * (g j).inner x v v) ∧
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
          1 / α ≤ (g j).tangentNorm x ((g j).gradient f x) ∧
            (g j).tangentNorm x ((g j).gradient f x) ≤ 1) ∧
        f ⁻¹' Icc a (3 * b / 2) ⊆ (g j).ball (p j) (2 * r) ∧
        {x : M j | ((g j).edist (p j) x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
          f ⁻¹' Icc a b := by
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    exists_eventually_wide_proper_regular_slabs_at_small_radii
      g D hc hsec p hgeo hconv
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr₀
  obtain ⟨ε, H, hε, hεr, hH, hslabs⟩ := hsmall r hr hrr₀
  let τ := 1 / (2 * max r 1)
  let a₀ := τ * (55 * r / 48)
  let a := τ * (7 * r / 6)
  let b := τ * (6 * r / 5)
  let C := modelVolume (m + 2) 1 (2 * r) / (a - a₀) *
    Real.exp ((((m + 1 : ℕ) : ℝ) * (τ * H) / (τ / 4) ^ 2) * (3 * b / 2 - a₀))
  let α := max 1 (max (1 / (τ / 4))
    (max (((τ * H) / (τ / 4)) * (3 * b / 2)) (C / a ^ (m + 1))))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτr : 0 < τ * r := mul_pos hτ hr
  have hτrle : τ * r ≤ 1 / 2 := by
    have hm : 0 < max r 1 := zero_lt_one.trans_le (le_max_right _ _)
    dsimp only [τ]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (mul_pos (by norm_num) hm)).mpr
    nlinarith only [le_max_left r 1]
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha₀a : a₀ < a := by dsimp only [a₀, a]; nlinarith
  have hab : a < b := by dsimp only [a, b]; nlinarith
  have hb : 3 * b / 2 ≤ 1 := by dsimp only [b]; nlinarith
  have hα : 0 < α := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨a, b, α, ha, hab, hb, hα, ?_⟩
  filter_upwards [hslabs] with j hj
  obtain ⟨f, hf, hproper, _, hband, hbounds⟩ := hj
  have hnorm := (D j).normalized_wide_regular_slab hf hr hε hεr hH (p j)
    hproper hband hbounds
  dsimp only at hnorm
  obtain ⟨_, _, _, _, _, _, _, hF, hproperF, hregF, hbandF, hboundsF⟩ := hnorm
  let F := fun x => τ * f x
  let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
  have hinside : Icc a₀ (3 * b / 2) ⊆ I := by
    intro t ht
    change τ * (9 * r / 8) < t ∧ t < τ * (15 * r / 8)
    dsimp only [a₀, b] at ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hsub : Icc a (3 * b / 2) ⊆ Icc a₀ (3 * b / 2) :=
    fun _ ht => ⟨ha₀a.le.trans ht.1, ht.2⟩
  have hball : F ⁻¹' Icc a₀ (3 * b / 2) ⊆ (g j).ball (p j) (2 * r) := by
    intro x hx
    let := (g j).toMetricSpace
    rw [← (g j).toMetricSpace_ball, Metric.mem_ball, dist_comm]
    exact (hbandF x (hinside hx)).2
  have hparams := (D j).regularLevel_annular_bounds_of_gradient_hessian_bounds
    (hc j) (hsec j) hF isOpen_Ioo hproperF
    (l := τ / 4) (H := τ * H) (a₀ := a₀) (a := a) (b := b)
    (by positivity) (by positivity) ha ha₀a hab hinside (by positivity) (p j)
    (fun x hx => ⟨(hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.1,
      (hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.2.1⟩)
    (fun x hx => (hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.2.2) hball
  change 0 < α ∧ _ at hparams
  obtain ⟨_, harea, hhess, hspeed⟩ := hparams
  refine ⟨F, hF, I, isOpen_Ioo, hproperF, hsub.trans hinside, hregF,
    harea, hhess, hspeed, (preimage_mono hsub).trans hball, ?_⟩
  intro x hx
  have hxlo : r < ((g j).edist (p j) x).toReal := by
    change 113 * r / 96 ≤ _ ∧ _ ≤ 19 * r / 16 at hx
    linarith [hx.1]
  have hxhi : ((g j).edist (p j) x).toReal < 2 * r := by
    change 113 * r / 96 ≤ _ ∧ _ ≤ 19 * r / 16 at hx
    linarith [hx.2]
  have happrox := abs_le.mp (hboundsF x hxlo hxhi).1
  have hlo : 7 * r / 6 ≤ ((g j).edist (p j) x).toReal - ε := by linarith [hx.1]
  have hhi : ((g j).edist (p j) x).toReal + ε ≤ 6 * r / 5 := by linarith [hx.2]
  have hlo' := mul_le_mul_of_nonneg_left hlo hτ.le
  have hhi' := mul_le_mul_of_nonneg_left hhi hτ.le
  change a ≤ F x ∧ F x ≤ b
  dsimp only [a, b, F]
  constructor <;> nlinarith only [hlo', hhi', happrox.1, happrox.2]


theorem exists_eventually_annular_induction_geometry_of_sectional_pointed_limit
    {m : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) (M j)]
    [∀ j, IsManifold (𝓡 (m + 2)) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric (m + 2) (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 (m + 2)) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    ∃ r a b α : ℝ, 0 < r ∧ 0 < a ∧ a < b ∧ 3 * b / 2 ≤ 1 ∧ 0 < α ∧
      ∀ᶠ j in atTop, ∃ (f : M j → ℝ) (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
        (I : Set ℝ), IsOpen I ∧ IsProperMap (I.restrictPreimage f) ∧
        Icc a (3 * b / 2) ⊆ I ∧
        (∀ x : M j, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ t ∈ Icc a (3 * b / 2), (g j).regularLevelArea hf t ≤ α * t ^ (m + 1)) ∧
        (∀ t ∈ Icc a (3 * b / 2), ∀ x, f x = t →
          ∀ v : TangentSpace (𝓡 (m + 2)) x,
            (g j).inner x ((D j).gradient f x) v = 0 →
            (D j).hessian f x v v / Real.sqrt ((D j).levelQ f x) ≤
              (α / t) * (g j).inner x v v) ∧
        (∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
          1 / α ≤ (g j).tangentNorm x ((g j).gradient f x) ∧
            (g j).tangentNorm x ((g j).gradient f x) ≤ 1) ∧
        f ⁻¹' Icc a (3 * b / 2) ⊆ (g j).ball (p j) (2 * r) ∧
        {x : M j | ((g j).edist (p j) x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
          f ⁻¹' Icc a b := by
  obtain ⟨r, hr, hsmall⟩ :=
    exists_eventually_annular_induction_geometry_at_small_radii g D hc hsec p hgeo hconv
  obtain ⟨a, b, α, ha, hab, hb, hα, hslabs⟩ := hsmall r hr le_rfl
  exact ⟨r, a, b, α, hr, ha, hab, hb, hα, hslabs⟩

end PoincareConjecture.RiemannianMetric
