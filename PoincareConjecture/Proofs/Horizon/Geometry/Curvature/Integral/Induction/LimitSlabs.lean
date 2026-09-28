import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SlabParameters
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Ascent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.AnnularStability
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.RiemannianLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.PuncturedAscent
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.PointedLimit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

private theorem exists_eventually_proper_regular_slabs_with_band_parameters
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ ε H : ℝ, 0 < ε ∧ ε < r / 128 ∧ 0 < H ∧
      ∀ a b : ℝ, a < b → r + ε < a → b < 2 * r - ε →
      ∀ᶠ j in atTop, ∃ f : M j → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
        IsProperMap ((Ioo a b).restrictPreimage f) ∧
        (∀ x : M j, f x ∈ Ioo a b →
          mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ x : M j, f x ∈ Ioo a b →
          r < ((g j).edist (p j) x).toReal ∧ ((g j).edist (p j) x).toReal < 2 * r) ∧
        ∀ x : M j, r < ((g j).edist (p j) x).toReal →
          ((g j).edist (p j) x).toReal < 2 * r →
          |f x - ((g j).edist (p j) x).toReal| ≤ ε ∧
          (1 : ℝ) / 4 ≤ (g j).tangentNorm x ((D j).gradient f x) ∧
          (g j).tangentNorm x ((D j).gradient f x) ≤ 2 ∧
          ∀ v : TangentSpace (𝓡 n) x,
            (D j).hessian f x v v ≤ H * (g j).inner x v v := by
  have hcurv : Poincare.Alexandrov.CurvatureGEnegOne Y.carrier :=
    Poincare.Alexandrov.curvatureGEnegOne_of_pointedGHConvergesUnbounded
      (fun j => (g j).curvatureGEnegOne_of_sectional_lower_bound (D j) (hc j) (hsec j)) hconv
  have hpacking (α : ℝ) (hα : 0 < α) : ∃ N : ℕ,
      Poincare.Alexandrov.ComparisonAnglePackingBound Y.carrier α N := by
    obtain ⟨N, hN⟩ := exists_comparisonAngle_packing_bound_of_sectional_pointed_limit n hα
    exact ⟨N, hN g p D hc hsec hconv⟩
  obtain ⟨s, hs, hascent⟩ := Poincare.Alexandrov.exists_pos_punctured_distance_ascent
    hcurv hgeo hpacking (c := (3 : ℝ) / 4) (by norm_num) (by norm_num) Y.base
  refine ⟨s / 4, by positivity, ?_⟩
  intro r hr hrr₀
  obtain ⟨T, ε₀, hT, hTr, hε₀, _, herr₀⟩ :=
    Poincare.CurvatureIntegral.exists_positive_slab_parameters hr 1
  let ε := min ε₀ (r / 256)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεr : ε < r / 128 := (min_le_right _ _).trans_lt (by linarith)
  have herr : 2 * ε / T +
      (4 / (3 * (r / 2 - T)) + 1 * (3 * r + T) / 4 + 1) * T / 2 < 1 / 4 := by
    have hquot : 2 * ε / T ≤ 2 * ε₀ / T :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)) hT.le
    linarith only [hquot, herr₀]
  let H := 4 / (3 * (r / 2 - T)) + (3 * r + T) / 4 + 1
  have hH : 0 < H := by
    have hden : 0 < r / 2 - T := by linarith
    dsimp only [H]
    positivity
  have hbuffer : 0 < r - T := by linarith
  have hlimit : ∀ y : Y.carrier, r - T ≤ dist Y.base y →
      dist Y.base y ≤ 2 * r + T → ∀ a : ℝ, 0 < a →
        ∃ q : Y.carrier, dist y q < a ∧
          (3 : ℝ) / 4 * dist y q < dist Y.base q - dist Y.base y := by
    intro y hy hy'
    apply hascent y (hbuffer.trans_le hy)
    linarith
  have hsource := eventually_annular_distance_ascent_of_pointedGHConvergesUnbounded
    g D hc (K := 1) zero_le_one hsec p hconv hbuffer
    (show (1 : ℝ) / 2 < 3 / 4 by norm_num) hlimit
  refine ⟨ε, H, hε, hεr, hH, ?_⟩
  intro a b hab hinner houter
  filter_upwards [hsource] with j hj
  let : ConnectedSpace (M j) := { toNonempty := ⟨p j⟩ }
  have hsmall : 2 * ε / T +
      (4 / (3 * (r / 2 - T)) + 1 * (3 * r + T) / 4 + 1) * T / 2 <
        (1 : ℝ) / 2 := by linarith only [herr]
  obtain ⟨f, hf, hproper, hreg, hband, hbound⟩ :=
    (g j).exists_proper_regular_slab_of_local_distance_ascent (D j) (hc j)
      (K := 1) zero_le_one (hsec j) (p j)
      (r₀ := r / 2) (r₁ := r) (R₀ := 2 * r) (R₁ := 3 * r)
      (T := T) (ε := ε) (η := 1) (c := (1 : ℝ) / 2)
      (a := a) (b := b)
      hT (by linarith) (by linarith) (by linarith) (by linarith)
      hε zero_lt_one (by norm_num) (by linarith) (by linarith)
      (by linarith) (by linarith) hsmall
      (fun y hy hy' => hj y hy.le hy'.le)
  refine ⟨f, hf, hproper, hreg, hband, ?_⟩
  intro x hx hx'
  obtain ⟨hvalue, hlower, hupper, hhessian⟩ := hbound x hx hx'
  refine ⟨hvalue, ?_, ?_, ?_⟩
  · have hL : (1 : ℝ) / 4 ≤ 1 / 2 - 2 * ε / T -
        (4 / (3 * (r / 2 - T)) + 1 * (3 * r + T) / 4 + 1) * T / 2 := by
      linarith only [herr]
    exact hL.trans hlower
  · simpa only [one_add_one_eq_two] using hupper
  · simpa only [H, one_mul] using hhessian

theorem exists_eventually_proper_regular_slabs_of_sectional_pointed_limit
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    ∃ r ε H : ℝ, 0 < r ∧ 0 < ε ∧ ε < r / 8 ∧ 0 < H ∧
      ∀ᶠ j in atTop, ∃ f : M j → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
        IsProperMap ((Ioo (5 * r / 4) (7 * r / 4)).restrictPreimage f) ∧
        (∀ x : M j, f x ∈ Ioo (5 * r / 4) (7 * r / 4) →
          mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ x : M j, f x ∈ Ioo (5 * r / 4) (7 * r / 4) →
          r < ((g j).edist (p j) x).toReal ∧ ((g j).edist (p j) x).toReal < 2 * r) ∧
        ∀ x : M j, r < ((g j).edist (p j) x).toReal →
          ((g j).edist (p j) x).toReal < 2 * r →
          |f x - ((g j).edist (p j) x).toReal| ≤ ε ∧
          (1 : ℝ) / 4 ≤ (g j).tangentNorm x ((D j).gradient f x) ∧
          (g j).tangentNorm x ((D j).gradient f x) ≤ 2 ∧
          ∀ v : TangentSpace (𝓡 n) x,
            (D j).hessian f x v v ≤ H * (g j).inner x v v := by
  obtain ⟨r, hr, hsmall⟩ :=
    exists_eventually_proper_regular_slabs_with_band_parameters g D hc hsec p hgeo hconv
  obtain ⟨ε, H, hε, hεr, hH, hslabs⟩ := hsmall r hr le_rfl
  refine ⟨r, ε, H, hr, hε, by linarith, hH, ?_⟩
  exact hslabs (5 * r / 4) (7 * r / 4) (by linarith) (by linarith) (by linarith)

theorem exists_eventually_wide_proper_regular_slabs_at_small_radii
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ ε H : ℝ, 0 < ε ∧ ε < r / 128 ∧ 0 < H ∧
      ∀ᶠ j in atTop, ∃ f : M j → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
        IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f) ∧
        (∀ x : M j, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
          mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ x : M j, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
          r < ((g j).edist (p j) x).toReal ∧ ((g j).edist (p j) x).toReal < 2 * r) ∧
        ∀ x : M j, r < ((g j).edist (p j) x).toReal →
          ((g j).edist (p j) x).toReal < 2 * r →
          |f x - ((g j).edist (p j) x).toReal| ≤ ε ∧
          (1 : ℝ) / 4 ≤ (g j).tangentNorm x ((D j).gradient f x) ∧
          (g j).tangentNorm x ((D j).gradient f x) ≤ 2 ∧
          ∀ v : TangentSpace (𝓡 n) x,
            (D j).hessian f x v v ≤ H * (g j).inner x v v := by
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    exists_eventually_proper_regular_slabs_with_band_parameters g D hc hsec p hgeo hconv
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr₀
  obtain ⟨ε, H, hε, hεr, hH, hslabs⟩ := hsmall r hr hrr₀
  refine ⟨ε, H, hε, hεr, hH, ?_⟩
  exact hslabs (9 * r / 8) (15 * r / 8) (by linarith) (by linarith) (by linarith)

theorem exists_eventually_wide_proper_regular_slabs_of_sectional_pointed_limit
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    ∃ r ε H : ℝ, 0 < r ∧ 0 < ε ∧ ε < r / 128 ∧ 0 < H ∧
      ∀ᶠ j in atTop, ∃ f : M j → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
        IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f) ∧
        (∀ x : M j, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
          mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        (∀ x : M j, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
          r < ((g j).edist (p j) x).toReal ∧ ((g j).edist (p j) x).toReal < 2 * r) ∧
        ∀ x : M j, r < ((g j).edist (p j) x).toReal →
          ((g j).edist (p j) x).toReal < 2 * r →
          |f x - ((g j).edist (p j) x).toReal| ≤ ε ∧
          (1 : ℝ) / 4 ≤ (g j).tangentNorm x ((D j).gradient f x) ∧
          (g j).tangentNorm x ((D j).gradient f x) ≤ 2 ∧
          ∀ v : TangentSpace (𝓡 n) x,
            (D j).hessian f x v v ≤ H * (g j).inner x v v := by
  obtain ⟨r, hr, hsmall⟩ :=
    exists_eventually_wide_proper_regular_slabs_at_small_radii g D hc hsec p hgeo hconv
  obtain ⟨ε, H, hε, hεr, hH, hslabs⟩ := hsmall r hr le_rfl
  exact ⟨r, ε, H, hr, hε, hεr, hH, hslabs⟩

end PoincareConjecture.RiemannianMetric
