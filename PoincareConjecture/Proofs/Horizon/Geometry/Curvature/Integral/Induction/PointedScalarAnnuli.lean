import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.PointedAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Annulus












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory Topology
open Poincare.GromovHausdorff Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric



theorem exists_eventually_radial_annulus_scalar_bound_at_small_radii
    {m : ℕ} (hm : 1 ≤ m) {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
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
      ∀ C : ℝ, 0 ≤ C → ∃ B : ℝ, 0 < B ∧
        ∀ᶠ j in atTop, ∃ (f : M j → ℝ)
          (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f) (I : Set ℝ),
          IsOpen I ∧ IsProperMap (I.restrictPreimage f) ∧
          Icc a (3 * b / 2) ⊆ I ∧
          (∀ x : M j, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
          let U := (g j).regularDomain hf
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI (t : ℝ) := openLevelSetChartedSpace hf U ((g j).regularDomain_regular hf)
            (m + 1) t
          letI (t : ℝ) := isManifold_openLevelSet hf U ((g j).regularDomain_regular hf)
            (m + 1) t
          let DL := fun t => (RiemannianMetric.regularLevelMetric
            hf U ((g j).regularDomain_regular hf) t (g j)).leviCivitaData
          (∀ t ∈ Icc a (3 * b / 2),
            (∫ z, max 0 ((DL t).scalarCurvature z)
              ∂(g j).regularLevelVolume hf U ((g j).regularDomain_regular hf) t) ≤
            C * (1 + ∫ z, (D j).levelSectionalError f (fun _ => 1) (α / t)
              (openLevelIncl f U t z)
              ∂(g j).regularLevelVolume hf U ((g j).regularDomain_regular hf) t)) →
          (∫ x in {x : M j | ((g j).edist (p j) x).toReal ∈
              Icc (113 * r / 96) (19 * r / 16)},
            max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ B := by
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    exists_eventually_annular_induction_geometry_at_small_radii
      g D hc hsec p hgeo hconv
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr₀
  obtain ⟨a, b, α, ha, hab, hb, hα, hslabs⟩ := hsmall r hr hrr₀
  refine ⟨a, b, α, ha, hab, hb, hα, ?_⟩
  intro C hC
  let Q := α * C + ((m + 2 : ℕ) : ℝ) ^ 2
  let L := α * C * (1 + ((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
    ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3)
  let B := 2 * (max Q L + 2 * α) * (1 + modelVolume (m + 2) 1 (2 * r))
  have hQ : 0 ≤ Q := add_nonneg (mul_nonneg hα.le hC) (sq_nonneg _)
  have hmax : 0 ≤ max Q L := hQ.trans (le_max_left Q L)
  have hcoefficient : 0 < 2 * (max Q L + 2 * α) := by positivity
  have hmodel : 0 ≤ modelVolume (m + 2) 1 (2 * r) :=
    modelVolume_nonneg (m + 2) zero_le_one (by positivity)
  have hB : 0 < B := mul_pos hcoefficient (by linarith only [hmodel])
  refine ⟨B, hB, ?_⟩
  filter_upwards [hslabs] with j hj
  obtain ⟨f, hf, I, hI, hproper, hslab, hreg, harea, hhess, hspeed, hball, hradial⟩ := hj
  refine ⟨f, hf, I, hI, hproper, hslab, hreg, ?_⟩
  dsimp only
  intro hind
  have hannulus := (D j).integral_scalarCurvature_posPart_inner_slab_le_of_level_induction
    hf hI hproper hreg ha hab hb (by omega : 2 ≤ m + 1) hα hC hslab
    (K := fun _ => 1) continuousOn_const (fun _ _ => zero_le_one)
    (fun x _ v w => hsec j x v w) harea hhess hspeed hind
  change (∫ x in f ⁻¹' Icc a b, max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤
    2 * (max Q L + 2 * α) *
      (1 + ∫ _ in f ⁻¹' Icc a (3 * b / 2), (1 : ℝ) ∂(g j).volumeMeasure) at hannulus
  have hcompact := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hslab
  have hintegrable := ((continuous_const (y := (0 : ℝ))).max
    (D j).continuous_scalarCurvature).continuousOn.integrableOn_compact hcompact
      (μ := (g j).volumeMeasure)
  have hbb : b ≤ 3 * b / 2 := by linarith only [ha, hab]
  have hinner : f ⁻¹' Icc a b ⊆ f ⁻¹' Icc a (3 * b / 2) :=
    preimage_mono (fun _ hx => ⟨hx.1, hx.2.trans hbb⟩)
  have hradialIntegral :
      (∫ x in {x : M j | ((g j).edist (p j) x).toReal ∈
          Icc (113 * r / 96) (19 * r / 16)},
        max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤
      ∫ x in f ⁻¹' Icc a b, max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure :=
    setIntegral_mono_set (hintegrable.mono_set hinner)
      (Eventually.of_forall (fun _ => le_max_left _ _)) (Eventually.of_forall hradial)
  have hvolume := measureReal_mono hball
    ((g j).volumeMeasure_ball_lt_top (hc j) (p j) (2 * r)).ne
  have hballVolume := (g j).volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    (p j) (by omega : 1 ≤ m + 2) (hc j) (D j) (hsec j) (by positivity : 0 < 2 * r)
  have hmass : (∫ _ in f ⁻¹' Icc a (3 * b / 2), (1 : ℝ) ∂(g j).volumeMeasure) ≤
      modelVolume (m + 2) 1 (2 * r) := by
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using hvolume.trans hballVolume
  exact hradialIntegral.trans (hannulus.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmass) hcoefficient.le))

theorem exists_eventually_radial_annulus_scalar_bound_of_sectional_pointed_limit
    {m : ℕ} (hm : 1 ≤ m) {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
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
      ∀ C : ℝ, 0 ≤ C → ∃ B : ℝ, 0 < B ∧
        ∀ᶠ j in atTop, ∃ (f : M j → ℝ)
          (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f) (I : Set ℝ),
          IsOpen I ∧ IsProperMap (I.restrictPreimage f) ∧
          Icc a (3 * b / 2) ⊆ I ∧
          (∀ x : M j, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
          let U := (g j).regularDomain hf
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI (t : ℝ) := openLevelSetChartedSpace hf U ((g j).regularDomain_regular hf)
            (m + 1) t
          letI (t : ℝ) := isManifold_openLevelSet hf U ((g j).regularDomain_regular hf)
            (m + 1) t
          let DL := fun t => (RiemannianMetric.regularLevelMetric
            hf U ((g j).regularDomain_regular hf) t (g j)).leviCivitaData
          (∀ t ∈ Icc a (3 * b / 2),
            (∫ z, max 0 ((DL t).scalarCurvature z)
              ∂(g j).regularLevelVolume hf U ((g j).regularDomain_regular hf) t) ≤
            C * (1 + ∫ z, (D j).levelSectionalError f (fun _ => 1) (α / t)
              (openLevelIncl f U t z)
              ∂(g j).regularLevelVolume hf U ((g j).regularDomain_regular hf) t)) →
          (∫ x in {x : M j | ((g j).edist (p j) x).toReal ∈
              Icc (113 * r / 96) (19 * r / 16)},
            max 0 ((D j).scalarCurvature x) ∂(g j).volumeMeasure) ≤ B := by

  obtain ⟨r, hr, hsmall⟩ :=
    exists_eventually_radial_annulus_scalar_bound_at_small_radii hm g D hc hsec p hgeo hconv
  obtain ⟨a, b, α, ha, hab, hb, hα, hbound⟩ := hsmall r hr le_rfl
  exact ⟨r, a, b, α, hr, ha, hab, hb, hα, hbound⟩

end PoincareConjecture.RiemannianMetric
