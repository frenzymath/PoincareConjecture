import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import PoincareConjecture.Definitions.Ch19.AnnulusComparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure LoopFamilyFlowInput (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (t₀ t₁ : ℝ) where
  time_ordered : t₀ < t₁
  flow : RicciFlow 3 M (Set.Icc t₀ t₁)
  compact : IsCompact (Set.univ : Set M)
  connected : IsConnected (Set.univ : Set M)
  hausdorff : T2Space M
  second_countable : SecondCountableTopology M
  basepoint : M
  pi_two_subsingleton : Subsingleton (HomotopyGroup.Pi 2 M basepoint)
  family : FreeTwoSphereFamily (M := M)
  family_basepoint : family.basepoint = basepoint
  family_null : ∀ c, IsNullHomotopicLoop (family.family c)
  filling_data : ∀ c, FillingAreaData (flow.metric t₀) (family.family c)

noncomputable def flowScalarCurvatureInfimum
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁)) (t : ℝ) : ℝ :=
  sInf (Set.range (fun x : M => (F.connection t).scalarCurvature x))

noncomputable def areaComparisonProfile
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁)) (a t : ℝ) : ℝ :=
  Real.exp (-(∫ s in t₀..t,
      sInf (Set.range (fun x : M => (F.connection s).scalarCurvature x)) / 2)) *
    (a - 2 * Real.pi * (∫ s in t₀..t,
      Real.exp (∫ v in t₀..s,
        sInf (Set.range (fun x : M => (F.connection v).scalarCurvature x)) / 2)))

structure DeformationRampFamily {t₀ t₁ : ℝ}
    (A : RampAmbientData (n := 3) (M := M) (t₀ := t₀) (t₁ := t₁))
    (approximation : FreeTwoSphereFamily (M := M)) where
  initial_bound : ℝ
  initial_bound_pos : 0 < initial_bound
  initial : ∀ lambda : Set.Ioo (0 : ℝ) 1, ∀ _c : LoopTwoSphere,
    RampInitialCurve A lambda.1
  initial_lift : ∀ lambda c,
    (initial lambda c).curve = canonicalRampLift (approximation.family c) lambda.1
  initial_length : ∀ lambda c, initialRampLength A (initial lambda c) ≤ initial_bound
  initial_curvature : ∀ lambda c,
    initialRampTotalCurvature A (initial lambda c) ≤ initial_bound
  solution : ∀ lambda c, RampFlowSolution A lambda.1 (initial lambda c)
  family : Set.Ioo (0 : ℝ) 1 → ℝ → FreeTwoSphereFamily (M := M)
  projection : ∀ lambda t, t ∈ Set.Icc t₀ t₁ → ∀ c x,
    periodicFreeLoop ((family lambda t).family c) x =
      ((solution lambda c).curve x t).1
  initial_family : ∀ lambda, family lambda t₀ = approximation
  continuous : ∀ lambda,
    Continuous (fun p : Set.Icc t₀ t₁ × LoopTwoSphere =>
      (family lambda p.1.1).family p.2)
  homotopic : ∀ lambda t, t ∈ Set.Icc t₀ t₁ →
    FreeTwoSphereHomotopic approximation (family lambda t)
  filling_data : ∀ lambda t, t ∈ Set.Icc t₀ t₁ → ∀ c,
    FillingAreaData (A.flow.metric t) ((family lambda t).family c)

structure EssentialAnnulusCurve where
  curve : ℝ → AnnulusCoordinates
  regular : ContDiff ℝ 1 curve
  winding : ℤ
  winding_ne_zero : winding ≠ 0
  horizontal_period : ∀ x,
    curve (x + rampPeriod) 0 = curve x 0 + (winding : ℝ) * rampPeriod
  vertical_period : ∀ x, curve (x + rampPeriod) 1 = curve x 1
  vertical_mem : ∀ x, curve x 1 ∈ Set.Icc (0 : ℝ) 1

noncomputable def essentialAnnulusCurveLength {t₀ t₁ : ℝ}
    {A : RampAmbientData (n := 3) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {lambda t : ℝ} {c₀ c₁ : ℝ → M × ℝ}
    (N : LiftedRampAnnulus A lambda t c₀ c₁) (q : EssentialAnnulusCurve) : ℝ :=
  rampTotalLength A (fun x _ => N.map (q.curve x)) t

structure LoopFamilyDeformation {t₀ t₁ : ℝ}
    (P : LoopFamilyFlowInput M t₀ t₁)
    (zeta : ℝ) where
  zeta_pos : 0 < zeta
  ambient : RampAmbientData (n := 3) (M := M) (t₀ := t₀) (t₁ := t₁)
  ambient_flow : ambient.flow = P.flow
  approximation : FreeTwoSphereFamily (M := M)
  approximation_homotopic : FreeTwoSphereHomotopic P.family approximation
  approximation_c2 : ∀ c, IsC2FreeLoop (approximation.family c)
  ramps : DeformationRampFamily ambient approximation
  common_B : ℝ
  common_B_pos : 0 < common_B
  terminal_window : t₁ - common_B⁻¹ ∈ Set.Icc t₀ t₁
  annulus_threshold : ℝ
  annulus_threshold_pos : 0 < annulus_threshold
  finite_net : RampFamilyAnnulusNet ambient approximation annulus_threshold
  pointwise_cutoff : LoopTwoSphere → ℝ
  pointwise_cutoff_pos : ∀ c, 0 < pointwise_cutoff c
  single_curve_alternative : ∀ c, ∀ lambda : Set.Ioo (0 : ℝ) 1,
    lambda.1 < pointwise_cutoff c →
      (∀ t ∈ Set.Icc (t₁ - common_B⁻¹) t₁,
        rampTotalLength ambient (ramps.solution lambda c).curve t < zeta / 2) ∨
      fillingArea (P.flow.metric t₁) ((ramps.family lambda t₁).family c) ≤
        areaComparisonProfile P.flow
          (fillingArea (P.flow.metric t₀) (approximation.family c)) t₁ + zeta / 2
  common_lambda : Set.Ioo (0 : ℝ) 1
  common_lambda_net : common_lambda.1 < finite_net.circumference_cutoff
  common_lambda_nodes : ∀ i,
    common_lambda.1 < pointwise_cutoff (finite_net.nodes i)
  net_bridge : ∀ c, ∃ i, ∃ N : LiftedRampAnnulus ambient common_lambda.1 t₀
    (ramps.initial common_lambda c).curve
    (ramps.initial common_lambda (finite_net.nodes i)).curve,
      N.area < annulus_threshold
  nondegeneration : ∀ t ∈ Set.Icc t₀ t₁, ∀ c c',
    ∀ N : LiftedRampAnnulus ambient common_lambda.1 t
      (fun x => (ramps.solution common_lambda c).curve x t)
      (fun x => (ramps.solution common_lambda c').curve x t),
      ∀ q : EssentialAnnulusCurve,
        common_lambda.1 * |(q.winding : ℝ)| ≤ essentialAnnulusCurveLength N q
  family : Set.Icc t₀ t₁ → FreeTwoSphereFamily (M := M)
  family_eq : ∀ t, family t = ramps.family common_lambda t.1
  endpoint_initial_homotopic :
    FreeTwoSphereHomotopic P.family
      (family ⟨t₀, by exact ⟨le_rfl, le_of_lt P.time_ordered⟩⟩)
  continuous : Continuous (fun p : Set.Icc t₀ t₁ × LoopTwoSphere =>
    (family p.1).family p.2)
  basepoint_fixed : ∀ s, (family s).basepoint = P.basepoint
  class_preserved : ∀ s,
    familySigmaClass (family s) = familySigmaClass P.family
  homotopic : ∀ s, FreeTwoSphereHomotopic P.family (family s)
  null_homotopic : ∀ s c, IsNullHomotopicLoop ((family s).family c)
  initial_area_close : ∀ c,
    |fillingArea (P.flow.metric t₀) ((family ⟨t₀, by
      exact ⟨le_rfl, P.time_ordered.le⟩⟩).family c) -
    fillingArea (P.flow.metric t₀) (P.family.family c)| < zeta
  short_or_area : ∀ c,
    freeLoopLength (P.flow.metric t₁) ((family ⟨t₁,
      by exact ⟨P.time_ordered.le, le_rfl⟩⟩).family c) < zeta ∨
    fillingArea (P.flow.metric t₁)
        ((family ⟨t₁, by exact ⟨P.time_ordered.le, le_rfl⟩⟩).family c) ≤
      areaComparisonProfile P.flow
        (fillingArea (P.flow.metric t₀)
          ((family ⟨t₀, by exact ⟨le_rfl, P.time_ordered.le⟩⟩).family c)) t₁ + zeta

end PoincareConjecture
