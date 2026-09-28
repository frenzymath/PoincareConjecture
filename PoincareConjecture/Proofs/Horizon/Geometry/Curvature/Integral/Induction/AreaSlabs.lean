import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.LimitSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.AreaGrowth










noncomputable section
set_option autoImplicit false

open Set Filter Topology
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

theorem exists_eventually_area_controlled_regular_slabs_of_sectional_pointed_limit
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (M j)]
    [∀ j, IsManifold (𝓡 (n + 1)) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric (n + 1) (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 (n + 1)) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    ∃ r ε H α : ℝ, 0 < r ∧ 0 < ε ∧ ε < r / 128 ∧ 0 < H ∧ 0 < α ∧
      ∀ᶠ j in atTop, ∃ (f : M j → ℝ) (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f),
        IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f) ∧
        (∀ x : M j, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
          mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ x : M j, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
          r < ((g j).edist (p j) x).toReal ∧ ((g j).edist (p j) x).toReal < 2 * r) ∧
        (∀ x : M j, r < ((g j).edist (p j) x).toReal →
          ((g j).edist (p j) x).toReal < 2 * r →
          |f x - ((g j).edist (p j) x).toReal| ≤ ε ∧
          (1 : ℝ) / 4 ≤ (g j).tangentNorm x ((D j).gradient f x) ∧
          (g j).tangentNorm x ((D j).gradient f x) ≤ 2 ∧
          ∀ v : TangentSpace (𝓡 (n + 1)) x,
            (D j).hessian f x v v ≤ H * (g j).inner x v v) ∧
        ∀ t ∈ Icc (7 * r / 6) (11 * r / 6),
          (g j).regularLevelArea hf t ≤ α * t ^ n := by
  obtain ⟨r, ε, H, hr, hε, hεr, hH, hslabs⟩ :=
    exists_eventually_wide_proper_regular_slabs_of_sectional_pointed_limit
      g D hc hsec p hgeo hconv
  let a := 55 * r / 48
  let d := 7 * r / 6
  let b := 11 * r / 6
  let C := 2 * modelVolume (n + 1) 1 (2 * r) / (d - a) *
    Real.exp (((n : ℝ) * H / ((1 : ℝ) / 4) ^ 2) * (b - a))
  let α := max 1 (C / d ^ n)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hα : 0 < α := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨r, ε, H, α, hr, hε, hεr, hH, hα, ?_⟩
  filter_upwards [hslabs] with j hj
  obtain ⟨f, hf, hproper, hreg, hband, hbounds⟩ := hj
  refine ⟨f, hf, hproper, hreg, hband, hbounds, ?_⟩
  have hinside : Icc a b ⊆ Ioo (9 * r / 8) (15 * r / 8) := by
    intro t ht
    dsimp only [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hball : f ⁻¹' Icc a b ⊆ (g j).ball (p j) (2 * r) := by
    intro x hx
    let := (g j).toMetricSpace
    rw [← (g j).toMetricSpace_ball, Metric.mem_ball, dist_comm]
    exact (hband x (hinside hx)).2
  have harea := (D j).regularLevelArea_le_of_gradient_hessian_bounds (hc j) (hsec j)
    hf isOpen_Ioo hproper (l := (1 : ℝ) / 4) (L := 2) (H := H)
    (a := a) (d := d) (b := b) (by norm_num) (by norm_num) hH.le
    (by dsimp only [a, d]; linarith) (by dsimp only [d, b]; linarith) hinside
    (by positivity : 0 < 2 * r) (p j)
    (fun x hx => ⟨(hbounds x (hband x hx).1 (hband x hx).2).2.1,
      (hbounds x (hband x hx).1 (hband x hx).2).2.2.1⟩)
    (fun x hx => (hbounds x (hband x hx).1 (hband x hx).2).2.2.2) hball
  intro t ht
  have hdt : d ≤ t := ht.1
  have hpow : d ^ n ≤ t ^ n := pow_le_pow_left₀ hd.le hdt n
  have hC : C ≤ α * d ^ n :=
    (div_le_iff₀ (pow_pos hd n)).mp (le_max_right 1 (C / d ^ n))
  exact (harea t ht).trans (hC.trans (mul_le_mul_of_nonneg_left hpow hα.le))

end PoincareConjecture.RiemannianMetric
