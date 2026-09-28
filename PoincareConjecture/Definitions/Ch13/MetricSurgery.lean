import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Definitions.Ch04.Pinching

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

structure MetricSurgeryConstants where
  C₀ : ℝ
  q : ℝ
  R₀ : ℝ
  delta₀ : ℝ
  C₀_pos : 0 < C₀
  C₀_gt_one : 1 < C₀
  q_pos : 0 < q
  q_gt_one : 1 < q
  R₀_pos : 0 < R₀
  delta₀_pos : 0 < delta₀
  delta₀_lt : delta₀ < 1 / 200
  comparison_delta : ℝ → ℝ
  comparison_delta_pos : ∀ eta : ℝ, 0 < eta → 0 < comparison_delta eta

def SurgeryPinchedOn {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (t : ℝ) (U : Set M) : Prop :=
  0 ≤ t ∧
    (∀ x ∈ U, -6 / (1 + 4 * t) ≤ D.scalarCurvature x) ∧
    (∀ x ∈ U, 0 < D.negativeCurvaturePart x →
      D.scalarCurvature x ≥ 2 * D.negativeCurvaturePart x *
        (Real.log (D.negativeCurvaturePart x) + Real.log (1 + t) - 3))

def SurgeryPinchedAt {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (t : ℝ) : Prop :=
  SurgeryPinchedOn D t Set.univ

structure MetricSurgeryInput (K : MetricSurgeryConstants)
    (g : RiemannianMetric 3 M) where
  neck : EpsilonNeck g
  time : ℝ
  delta_le : neck.epsilon ≤ K.delta₀
  scalar_large : K.R₀ ≤ neck.connection.scalarCurvature neck.center
  pinched : SurgeryPinchedOn neck.connection time neck.carrier

def SurgeryProfileLargeQ (g₀ : StandardInitialMetric)
    (K : MetricSurgeryConstants) : Prop :=
  100 * (4 + g₀.cylindrical_end.radius) ^ 2 < K.q ∧
    ∀ s : ℝ, 0 < s → s ≤ 4 + g₀.cylindrical_end.radius →
      (K.q ^ 2 / s ^ 4) * Real.exp (-K.q / s) < 1 / 100

noncomputable def surgeryMetricCoefficient {N : Type v}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) (f : StandardCapSpace → N)
    (a b : Fin 3) (p : StandardCapSpace) : ℝ :=
  g.inner (f p)
    (mfderiv (𝓡 3) (𝓡 3) f p (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (mfderiv (𝓡 3) (𝓡 3) f p (EuclideanSpace.basisFun (Fin 3) ℝ b))

noncomputable def surgeryCapPullback {N : Type v}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) (f : StandardCapSpace → N) :
    CovariantTensorEvaluation 3 StandardCapSpace 2 :=
  fun x v => g.inner (f x)
    (mfderiv (𝓡 3) (𝓡 3) f x (v 0))
    (mfderiv (𝓡 3) (𝓡 3) f x (v 1))

structure SurgeryCapClose (g₀ : StandardInitialMetric)
    (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
    (tip : S.carrier) (scale eta : ℝ) where
  eta_pos : 0 < eta
  scale_pos : 0 < scale
  map : StandardCapSpace → S.carrier
  inverse : S.carrier → StandardCapSpace
  map_tip : map 0 = tip
  map_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map (g₀.metric.ball 0 eta⁻¹)
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse
    (map '' g₀.metric.ball 0 eta⁻¹)
  image_contains : g.ball tip (scale * eta⁻¹) ⊆
    map '' g₀.metric.ball 0 eta⁻¹
  left_inverse : Set.LeftInvOn inverse map (g₀.metric.ball 0 eta⁻¹)
  right_inverse : Set.LeftInvOn map inverse (map '' g₀.metric.ball 0 eta⁻¹)
  coefficient_smooth : ∀ a b,
    ContDiffOn ℝ ∞ (surgeryMetricCoefficient g map a b)
      (g₀.metric.ball 0 eta⁻¹)

  jets : ∃ bound : ℝ, bound < eta ^ 2 ∧
    ∀ p ∈ g₀.metric.ball 0 eta⁻¹,
      singularMetricJetErrorSquared g₀.metric g₀.connection
        (fun x v => scale⁻¹ ^ 2 * surgeryCapPullback g map x v)
        ⌊eta⁻¹⌋₊ p ≤ bound

structure MetricSurgeryResult (g₀ : StandardInitialMetric)
    {K : MetricSurgeryConstants} {g : RiemannianMetric 3 M}
    (I : MetricSurgeryInput K g) where

  q_profile : SurgeryProfileLargeQ g₀ K
  output : GeneralizedSliceCarrier.{u}
  metric : RiemannianMetric 3 output.carrier
  connection : LeviCivitaData metric
  tip : output.carrier
  open_ball_model : Nonempty (output.carrier ≃ₜ ULift.{u} StandardCapSpace)
  collapse : M → output.carrier
  collapse_continuous : ContinuousOn collapse I.neck.carrier
  retained_inverse : output.carrier → M

  retained_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ collapse
    (I.neck.region (-I.neck.epsilon⁻¹) 1)
  retained_left_inverse : Set.LeftInvOn retained_inverse collapse
    (I.neck.region (-I.neck.epsilon⁻¹) 1)
  retained_right_inverse : Set.RightInvOn retained_inverse collapse
    (Set.range collapse)
  retained_metric : ∀ x ∈ I.neck.region (-I.neck.epsilon⁻¹) 0 ∪ I.neck.central_sphere,
    ∀ v w : TangentSpace (𝓡 3) x,
      metric.inner (collapse x)
        (mfderiv (𝓡 3) (𝓡 3) collapse x v)
        (mfderiv (𝓡 3) (𝓡 3) collapse x w) = g.inner x v w

  retained_closed_isometry :
    ∀ x ∈ I.neck.region (-I.neck.epsilon⁻¹) 0 ∪ I.neck.central_sphere,
      ∀ y ∈ I.neck.region (-I.neck.epsilon⁻¹) 0 ∪ I.neck.central_sphere,
        intrinsicEDist metric
            (collapse '' (I.neck.region (-I.neck.epsilon⁻¹) 0 ∪
              I.neck.central_sphere)) (collapse x) (collapse y) =
          intrinsicEDist g
            (I.neck.region (-I.neck.epsilon⁻¹) 0 ∪ I.neck.central_sphere) x y
  distance_decreasing : ∀ x ∈ I.neck.carrier, ∀ y ∈ I.neck.carrier,
    metric.edist (collapse x) (collapse y) ≤
      intrinsicEDist g I.neck.carrier x y
  cap_map : StandardCapSpace → output.carrier
  cap_inverse : output.carrier → StandardCapSpace
  cap_map_tip : cap_map 0 = tip

  cap_map_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ cap_map
    (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5))
  cap_left_inverse : Set.LeftInvOn cap_inverse cap_map
    (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5))
  cap_right_inverse : Set.RightInvOn cap_inverse cap_map
    (cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5))
  cap_inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ cap_inverse
    (cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5))
  output_cover : (collapse '' I.neck.region (-I.neck.epsilon⁻¹) 0) ∪
    closure (cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) = Set.univ
  cap_exterior : (closure (cap_map ''
    g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)))ᶜ =
      collapse '' I.neck.region (-I.neck.epsilon⁻¹) 0
  cap_boundary : collapse '' I.neck.central_sphere =
    frontier (cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))
  collapse_positive_cap : collapse '' I.neck.region 0 I.neck.epsilon⁻¹ ⊆
    closure (cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))
  collapse_positive_tail : ∃ b : ℝ,
    0 < b ∧ b < I.neck.epsilon⁻¹ ∧
      ∀ x ∈ I.neck.carrier,
        b ≤ (I.neck.coordinate_inverse x).2 → collapse x = tip
  cap_inner_ball : metric.ball tip (I.neck.scale * (g₀.cylindrical_end.radius + 3)) ⊆
    cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)
  cap_outer_ball : cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) ⊆
    metric.ball tip (I.neck.scale * (g₀.cylindrical_end.radius + 5))
  positive_sectional : ∀ x ∈ cap_map ''
      {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 3)},
    ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair metric x v w →
        0 < connection.sectionalCurvature x v w
  pinched : SurgeryPinchedAt connection I.time
  standard_close : ∀ eta : ℝ, 0 < eta →
    I.neck.epsilon ≤ K.comparison_delta eta →
      Nonempty (SurgeryCapClose g₀ output metric tip I.neck.scale eta)

  positive_sectional_preserved :
    (∀ x ∈ I.neck.carrier, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w →
        0 < I.neck.connection.sectionalCurvature x v w) →
    ∀ x : output.carrier, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair metric x v w →
        0 < connection.sectionalCurvature x v w

  retained_inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ retained_inverse
    (collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1)

  cap_closed_image : cap_map ''
      {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 4)} =
    closure (cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))

end PoincareConjecture
