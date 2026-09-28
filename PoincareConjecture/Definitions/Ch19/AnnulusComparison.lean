import PoincareConjecture.Definitions.Ch19.RampEstimates
import PoincareConjecture.Definitions.Ch01.Curvature

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

abbrev AnnulusCoordinates := EuclideanSpace ℝ (Fin 2)

noncomputable def annulusPoint (x s : ℝ) : AnnulusCoordinates := !₂[x, s]

def rampAnnulusDomain : Set AnnulusCoordinates :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ rampPeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}

def standardAnnulusDomain : Set AnnulusCoordinates :=
  {p | 1 ≤ ‖p‖ ∧ ‖p‖ ≤ 2}

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
variable {t₀ t₁ : ℝ}

noncomputable def rampAnnulusTangent
    (f : AnnulusCoordinates → M × ℝ) (p : AnnulusCoordinates)
    (i : Fin 2) : RampTangent n M (f p).1 :=
  (mfderiv (𝓡 2) (𝓡 n) (fun q => (f q).1) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i),
    fderiv ℝ (fun q : AnnulusCoordinates => (f q).2) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i))

noncomputable def rampAnnulusAreaDensity
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (f : AnnulusCoordinates → M × ℝ) (t : ℝ) (p : AnnulusCoordinates) : ℝ :=
  Real.sqrt (max 0 (Matrix.det (fun i j : Fin 2 =>
    rampMetricInner A t (f p).1 (rampAnnulusTangent f p i)
      (rampAnnulusTangent f p j))))

noncomputable def rampAnnulusArea
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (f : AnnulusCoordinates → M × ℝ) (t : ℝ) : ℝ :=
  ∫ p in rampAnnulusDomain, rampAnnulusAreaDensity A f t p

noncomputable def projectedAnnulusAreaDensity
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (f : AnnulusCoordinates → M × ℝ) (t : ℝ) (p : AnnulusCoordinates) : ℝ :=
  let v := rampAnnulusTangent f p
  Real.sqrt (max 0 (Matrix.det (fun i j : Fin 2 =>
    (A.flow.metric t).inner (f p).1 (v i).1 (v j).1)))

noncomputable def projectedAnnulusArea
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (f : AnnulusCoordinates → M × ℝ) (t : ℝ) : ℝ :=
  ∫ p in rampAnnulusDomain, projectedAnnulusAreaDensity A f t p

structure LiftedRampAnnulus
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (circumference t : ℝ) (c₀ c₁ : ℝ → M × ℝ) where
  map : AnnulusCoordinates → M × ℝ
  horizontal_regular : ContMDiff (𝓡 2) (𝓡 n) 1 (fun p => (map p).1)
  vertical_regular : ContDiff ℝ 1 (fun p => (map p).2)
  lower_boundary : ∀ x : ℝ, map (annulusPoint x 0) = c₀ x
  winding : ℤ
  upper_horizontal : ∀ x : ℝ, (map (annulusPoint x 1)).1 = (c₁ x).1
  upper_vertical : ∀ x : ℝ,
    (map (annulusPoint x 1)).2 = (c₁ x).2 + winding * circumference
  horizontal_periodic : ∀ x s,
    (map (annulusPoint (x + rampPeriod) s)).1 = (map (annulusPoint x s)).1
  lift_degree : ∀ x s,
    (map (annulusPoint (x + rampPeriod) s)).2 =
      (map (annulusPoint x s)).2 + circumference
  area_integrable : MeasureTheory.IntegrableOn
    (rampAnnulusAreaDensity A map t) rampAnnulusDomain MeasureTheory.volume
  projected_area_integrable : MeasureTheory.IntegrableOn
    (projectedAnnulusAreaDensity A map t) rampAnnulusDomain MeasureTheory.volume

noncomputable def LiftedRampAnnulus.area
    {A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference t : ℝ} {c₀ c₁ : ℝ → M × ℝ}
    (N : LiftedRampAnnulus A circumference t c₀ c₁) : ℝ :=
  rampAnnulusArea A N.map t

noncomputable def LiftedRampAnnulus.projectedArea
    {A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference t : ℝ} {c₀ c₁ : ℝ → M × ℝ}
    (N : LiftedRampAnnulus A circumference t c₀ c₁) : ℝ :=
  projectedAnnulusArea A N.map t

noncomputable def leastRampAnnulusArea
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (circumference t : ℝ) (c₀ c₁ : ℝ → M × ℝ) : ℝ :=
  sInf (Set.range (fun N : LiftedRampAnnulus A circumference t c₀ c₁ => N.area))

structure RampSlice
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (circumference t : ℝ) where
  curve : ℝ → M × ℝ
  horizontal_periodic : ∀ x, (curve (x + rampPeriod)).1 = (curve x).1
  lift_degree : ∀ x, (curve (x + rampPeriod)).2 = (curve x).2 + circumference
  spatial_regular : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 2 (fun x => (curve x).1)
  circle_regular : ContDiff ℝ 2 (fun x => (curve x).2)
  positive_circle_component : ∀ x,
    0 < rampCircleComponent A (fun y _ => curve y) x t

noncomputable def rampFlowSlice
    {A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference : ℝ} {initial : RampInitialCurve A circumference}
    (S : RampFlowSolution A circumference initial) (t : ℝ)
    (ht : t ∈ Set.Icc t₀ t₁) : RampSlice A circumference t where
  curve := fun x => S.curve x t
  horizontal_periodic := fun x => S.parameter_period x t
  lift_degree := fun x => S.degree_one_lift x t
  spatial_regular := S.spatial_regular t ht
  circle_regular := S.circle_regular t ht
  positive_circle_component := S.positive_circle_component t ht

noncomputable def rampSliceArcLength
    {A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference t : ℝ} (c : RampSlice A circumference t) (a b : ℝ) : ℝ :=
  rampArcLength A (fun x _ => c.curve x) t a b

noncomputable def rampSliceLength
    {A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference t : ℝ} (c : RampSlice A circumference t) : ℝ :=
  rampSliceArcLength c 0 rampPeriod

noncomputable def rampSliceCurvatureIntegral
    {A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference t : ℝ} (c : RampSlice A circumference t) (a b : ℝ) : ℝ :=
  rampArcTotalCurvature A (fun x _ => c.curve x) t a b

structure RampAnnulusFlowPair
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (circumference : ℝ) where
  initial₀ : RampInitialCurve A circumference
  initial₁ : RampInitialCurve A circumference
  solution₀ : RampFlowSolution A circumference initial₀
  solution₁ : RampFlowSolution A circumference initial₁

noncomputable def rampPairAnnulusArea
    {A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference : ℝ} (Q : RampAnnulusFlowPair A circumference) (t : ℝ) : ℝ :=
  leastRampAnnulusArea A circumference t
    (fun x => Q.solution₀.curve x t) (fun x => Q.solution₁.curve x t)

noncomputable def rampAmbientCurvatureSupremum
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)) (t : ℝ) : ℝ :=
  sSup (Set.range (fun x : M => (A.flow.connection t).curvatureTensorNorm x))

def AnnulusForwardDerivativeBound (f : ℝ → ℝ) (b t : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
    (f (t + h) - f t) / h ≤ b + eta

noncomputable def intrinsicAnnulusBoundary (radius x : ℝ) : AnnulusCoordinates :=
  !₂[radius * Real.cos x, radius * Real.sin x]

noncomputable def intrinsicBoundarySpeed
    (g : RiemannianMetric 2 AnnulusCoordinates) (radius x : ℝ) : ℝ :=
  g.tangentNorm (intrinsicAnnulusBoundary radius x)
    (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) x)

noncomputable def intrinsicBoundaryLength
    (g : RiemannianMetric 2 AnnulusCoordinates) (radius a b : ℝ) : ℝ :=
  ∫ x in a..b, intrinsicBoundarySpeed g radius x

noncomputable def intrinsicBoundaryUnitTangent
    (g : RiemannianMetric 2 AnnulusCoordinates) (radius x : ℝ) :
    TangentSpace (𝓡 2) (intrinsicAnnulusBoundary radius x) :=
  (intrinsicBoundarySpeed g radius x)⁻¹ •
    curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) x

noncomputable def intrinsicGeodesicCurvature
    (g : RiemannianMetric 2 AnnulusCoordinates) (D : LeviCivitaData g)
    (radius x : ℝ) : ℝ :=
  g.tangentNorm (intrinsicAnnulusBoundary radius x)
    ((intrinsicBoundarySpeed g radius x)⁻¹ •
      rampHorizontalCovariantDerivative D (intrinsicAnnulusBoundary radius)
        (fun y => intrinsicBoundaryUnitTangent g radius y) x)

noncomputable def intrinsicGeodesicCurvatureIntegral
    (g : RiemannianMetric 2 AnnulusCoordinates) (D : LeviCivitaData g)
    (radius a b : ℝ) : ℝ :=
  ∫ x in a..b, intrinsicGeodesicCurvature g D radius x *
    intrinsicBoundarySpeed g radius x

noncomputable def intrinsicAnnulusArea
    (g : RiemannianMetric 2 AnnulusCoordinates) : ℝ :=
  ∫ p in standardAnnulusDomain,
    Real.sqrt (max 0 (Matrix.det (fun i j : Fin 2 =>
      g.inner p (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j))))

structure IntrinsicAnnulus where
  metric : RiemannianMetric 2 AnnulusCoordinates
  connection : LeviCivitaData metric

def IntrinsicAnnulus.GaussianCurvatureBound (N : IntrinsicAnnulus) (K : ℝ) : Prop :=
  ∀ p ∈ standardAnnulusDomain, N.connection.scalarCurvature p / 2 ≤ K

def IntrinsicAnnulus.SmallBoundaryTurning (N : IntrinsicAnnulus) (delta r : ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → b ≤ a + rampPeriod →
    intrinsicBoundaryLength N.metric 1 a b ≤ r →
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b < delta

end PoincareConjecture

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
variable {t₀ t₁ : ℝ}

structure NullHomotopicRampProjection
    {A : RampAmbientData (n := 3) (M := M) (t₀ := t₀) (t₁ := t₁)}
    {circumference : ℝ} {initial : RampInitialCurve A circumference}
    (S : RampFlowSolution A circumference initial) where
  loop : ℝ → C1FreeLoopSpace (M := M)
  projection : ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
    periodicFreeLoop (loop t) x = (S.curve x t).1
  null_homotopic : ∀ t ∈ Set.Icc t₀ t₁, IsNullHomotopicLoop (loop t)
  filling_data : ∀ t ∈ Set.Icc t₀ t₁,
    FillingAreaData (A.flow.metric t) (loop t)

structure RampFamilyAnnulusNet
    (A : RampAmbientData (n := 3) (M := M) (t₀ := t₀) (t₁ := t₁))
    (family : FreeTwoSphereFamily (M := M)) (mu : ℝ) where
  node_count : ℕ
  nodes : Fin node_count → LoopTwoSphere
  circumference_cutoff : ℝ
  circumference_cutoff_positive : 0 < circumference_cutoff
  circumference_cutoff_le_one : circumference_cutoff ≤ 1
  covers : ∀ c : LoopTwoSphere, ∃ i : Fin node_count,
    ∀ circumference : ℝ, 0 < circumference → circumference < circumference_cutoff →
      ∃ N : LiftedRampAnnulus A circumference t₀
        (canonicalRampLift (family.family c) circumference)
        (canonicalRampLift (family.family (nodes i)) circumference), N.area < mu

noncomputable def rampScalarCurvatureInfimum
    (A : RampAmbientData (n := 3) (M := M) (t₀ := t₀) (t₁ := t₁)) (t : ℝ) : ℝ :=
  sInf (Set.range (fun x : M => (A.flow.connection t).scalarCurvature x))

noncomputable def rampAreaComparisonProfile
    (A : RampAmbientData (n := 3) (M := M) (t₀ := t₀) (t₁ := t₁))
    (a t : ℝ) : ℝ :=
  Real.exp (-(∫ s in t₀..t, rampScalarCurvatureInfimum A s / 2)) *
    (a - 2 * Real.pi * (∫ s in t₀..t,
      Real.exp (∫ v in t₀..s, rampScalarCurvatureInfimum A v / 2)))

end PoincareConjecture
