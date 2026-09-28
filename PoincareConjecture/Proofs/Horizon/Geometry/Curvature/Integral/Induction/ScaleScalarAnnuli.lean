import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleAnnulusBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RiemannianMetric

def scaleScalarAnnulusConstant (m : ℕ) (C : ℝ) : ℝ :=
  let α := scaleAnnularInductionConstant m
  let Q := α * C + ((m + 2 : ℕ) : ℝ) ^ 2
  let P := α * C * (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
    ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3)
  let V := euclideanUnitBallVolume (m + 2) *
    2 ^ (m + 2) * Real.exp (2 * ((m + 1 : ℕ) : ℝ))
  2 * Q * V + 3 * α * C + 2 * P + 4 * α

theorem scaleScalarAnnulusConstant_pos (m : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 < scaleScalarAnnulusConstant m C := by
  unfold scaleScalarAnnulusConstant
  positivity [scaleAnnularInductionConstant_pos m, euclideanUnitBallVolume_pos (m + 2)]

private theorem modelVolume_two_mul_le_scalar_power (m : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    modelVolume (m + 2) 1 (2 * r) ≤
      (euclideanUnitBallVolume (m + 2) * 2 ^ (m + 2) *
        Real.exp (2 * ((m + 1 : ℕ) : ℝ))) * r ^ m := by
  have h := modelVolume_le_exp_mul_zero (n := m + 2) (κ := 1)
    zero_le_one (by positivity : 0 ≤ 2 * r)
  rw [modelVolume_zero_curvature (by omega : 1 ≤ m + 2)] at h
  simp only [show m + 2 - 1 = m + 1 by omega, Real.sqrt_one, one_mul] at h
  calc
    _ ≤ euclideanUnitBallVolume (m + 2) * (2 * r) ^ (m + 2) *
        Real.exp (((m + 1 : ℕ) : ℝ) * (2 * r)) := h
    _ ≤ euclideanUnitBallVolume (m + 2) * (2 * r) ^ (m + 2) *
        Real.exp (2 * ((m + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) (m + 1)]))
      exact mul_nonneg (euclideanUnitBallVolume_nonneg _) (pow_nonneg (by positivity) _)
    _ = (euclideanUnitBallVolume (m + 2) * 2 ^ (m + 2) *
        Real.exp (2 * ((m + 1 : ℕ) : ℝ))) * r ^ (m + 2) := by
      rw [mul_pow]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr.le hr1 (by omega : m ≤ m + 2))
      positivity [euclideanUnitBallVolume_pos (m + 2)]

theorem exists_radial_annulus_scalar_bound_with_dimensional_constant
    {m : ℕ} (hm : 1 ≤ m) {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          (1 : ℝ) / 2 * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    let a := 7 * r / 12
    let b := 3 * r / 5
    let α := scaleAnnularInductionConstant m
    let I := Ioo (9 * r / 16) (15 * r / 16)
    ∃ (f : M → ℝ) (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f),
      IsProperMap (I.restrictPreimage f) ∧ Icc a (3 * b / 2) ⊆ I ∧
      (∀ x : M, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      f ⁻¹' Icc a (3 * b / 2) ⊆ g.ball p (2 * r) ∧
      {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
        f ⁻¹' Icc a b ∧
      let U := g.regularDomain hf
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
      letI (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
      let DL := fun t => (RiemannianMetric.regularLevelMetric
        hf U (g.regularDomain_regular hf) t g).leviCivitaData
      ∀ C : ℝ, 0 ≤ C →
        (∀ t ∈ Icc a (3 * b / 2),
          (∫ z, max 0 ((DL t).scalarCurvature z)
            ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
          C * (r ^ (m - 1) + ∫ z,
            D.levelSectionalError f (fun _ => 1) (α / t) (openLevelIncl f U t z)
            ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t)) →
        (∫ x in {x : M | (g.edist p x).toReal ∈
            Icc (113 * r / 96) (19 * r / 16)},
          max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
          scaleScalarAnnulusConstant m C * r ^ m := by
  let a := 7 * r / 12
  let b := 3 * r / 5
  let α := scaleAnnularInductionConstant m
  obtain ⟨ha, hab, _, hα, f, hf, hproper, hslab, hreg, harea, hhess, hspeed,
      hball, hradial⟩ :=
    g.exists_annular_induction_geometry_with_dimensional_constant D hc hsec p hr hr1 hascent
  refine ⟨f, hf, hproper, hslab, hreg, hball, hradial, ?_⟩
  dsimp only
  intro C hC hind
  let Q := α * C + ((m + 2 : ℕ) : ℝ) ^ 2
  let P := α * C * (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
    ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3)
  let V := euclideanUnitBallVolume (m + 2) *
    2 ^ (m + 2) * Real.exp (2 * ((m + 1 : ℕ) : ℝ))
  have hQ : 0 ≤ Q := add_nonneg (mul_nonneg hα.le hC) (sq_nonneg _)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hannulus := D.integral_scalarCurvature_posPart_inner_slab_le_of_scaled_level_induction
    hf isOpen_Ioo hproper hreg ha hab (by omega : 2 ≤ m + 1) hα hC
    (κ := r ^ (m - 1)) (pow_nonneg hr.le _) hslab
    (K := fun _ => 1) continuousOn_const (fun _ _ => zero_le_one)
    (fun x _ v w => hsec x v w) harea hhess hspeed hind
  change (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
    2 * Q * (∫ _ in f ⁻¹' Icc a (3 * b / 2), (1 : ℝ) ∂g.volumeMeasure) +
      3 * α * C * r ^ (m - 1) * b + 2 * P * (3 * b / 2) ^ m + 4 * α * b ^ m at hannulus
  have hcompact := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hslab
  have hintegrable := ((continuous_const (y := (0 : ℝ))).max
    D.continuous_scalarCurvature).continuousOn.integrableOn_compact hcompact
      (μ := g.volumeMeasure)
  have hbpos : 0 < b := ha.trans hab
  have hbb : b ≤ 3 * b / 2 := by linarith only [hbpos]
  have hinner : f ⁻¹' Icc a b ⊆ f ⁻¹' Icc a (3 * b / 2) :=
    preimage_mono (fun _ hx => ⟨hx.1, hx.2.trans hbb⟩)
  have hradialIntegral :
      (∫ x in {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      ∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure :=
    setIntegral_mono_set (hintegrable.mono_set hinner)
      (Eventually.of_forall (fun _ => le_max_left _ _)) (Eventually.of_forall hradial)
  have hvolume := measureReal_mono hball (g.volumeMeasure_ball_lt_top hc p (2 * r)).ne
  have hballVolume := g.volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    p (by omega : 1 ≤ m + 2) hc D hsec (by positivity : 0 < 2 * r)
  have hmass : (∫ _ in f ⁻¹' Icc a (3 * b / 2), (1 : ℝ) ∂g.volumeMeasure) ≤
      V * r ^ m := by
    have hmodel := hvolume.trans hballVolume |>.trans (modelVolume_two_mul_le_scalar_power m hr hr1)
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using hmodel
  have hbr : b ≤ r := by dsimp only [b]; linarith only [hr]
  have houterr : 3 * b / 2 ≤ r := by dsimp only [b]; linarith only [hr]
  have hκb : r ^ (m - 1) * b ≤ r ^ m := by
    calc
      r ^ (m - 1) * b ≤ r ^ (m - 1) * r :=
        mul_le_mul_of_nonneg_left hbr (pow_nonneg hr.le _)
      _ = r ^ m := by rw [← pow_succ]; congr 1; omega
  have hκterm := mul_le_mul_of_nonneg_left hκb
    (show 0 ≤ 3 * α * C by positivity)
  have houterterm := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (show 0 ≤ 3 * b / 2 by positivity) houterr m)
    (show 0 ≤ 2 * P by positivity)
  have hinnerterm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbpos.le hbr m)
    (show 0 ≤ 4 * α by positivity)
  have hmassterm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2 * Q by positivity)
  apply hradialIntegral.trans (hannulus.trans ?_)
  change _ ≤ (2 * Q * V + 3 * α * C + 2 * P + 4 * α) * r ^ m
  nlinarith only [hκterm, houterterm, hinnerterm, hmassterm]

end PoincareConjecture.RiemannianMetric
