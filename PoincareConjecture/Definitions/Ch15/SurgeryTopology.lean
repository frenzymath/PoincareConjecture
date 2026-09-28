import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Definitions.Ch09.ShrinkingSoliton
import Mathlib.Logic.Relation










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


structure SurgeryBallEmbedding (A : GeneralizedSliceCarrier.{u}) where
  map : StandardCapSpace → A.carrier
  inverse : A.carrier → StandardCapSpace
  map_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map (Metric.ball 0 2)
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse (map '' Metric.ball 0 2)
  left_inverse : Set.LeftInvOn inverse map (Metric.ball 0 2)
  right_inverse : Set.LeftInvOn map inverse (map '' Metric.ball 0 2)
  open_embedding : Topology.IsOpenEmbedding
    (fun x : Metric.ball (0 : StandardCapSpace) 2 => map x.1)

def SurgeryBallEmbedding.closedBall {A : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A) : Set A.carrier :=
  B.map '' Metric.closedBall 0 1



structure SmoothConnectedSumData (A B C : GeneralizedSliceCarrier.{u}) where
  first_ball : SurgeryBallEmbedding A
  second_ball : SurgeryBallEmbedding B
  first_region : Set C.carrier
  second_region : Set C.carrier
  first_open : IsOpen first_region
  second_open : IsOpen second_region
  first_identify : SurgeryRegionEquivalence A C first_ball.closedBallᶜ first_region
  second_identify : SurgeryRegionEquivalence B C second_ball.closedBallᶜ second_region
  regions_disjoint : Disjoint first_region second_region
  sphere_gluing : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞
  collar : RoundCylinderSpace → C.carrier
  collar_inverse : C.carrier → RoundCylinderSpace
  collar_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ collar
    (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  collar_inverse_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
    collar_inverse (collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
  collar_left_inverse : Set.LeftInvOn collar_inverse collar
    (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  collar_right_inverse : Set.LeftInvOn collar collar_inverse
    (collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
  collar_open : IsOpen (collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
  negative_gluing : ∀ z : UnitTwoSphere, ∀ s ∈ Set.Ioo (-1 : ℝ) 0,
    collar (z, s) = first_identify.map (first_ball.map ((1 - s) • z.1))
  positive_gluing : ∀ z : UnitTwoSphere, ∀ s ∈ Set.Ioo (0 : ℝ) 1,
    collar (z, s) = second_identify.map
      (second_ball.map ((1 + s) • (sphere_gluing z).1))
  central_disjoint : Disjoint (collar '' (Set.univ ×ˢ ({0} : Set ℝ)))
    (first_region ∪ second_region)
  cover : first_region ∪ second_region ∪
    (collar '' (Set.univ ×ˢ ({0} : Set ℝ))) = Set.univ

structure SmoothDisjointUnionData {n : ℕ}
    (pieces : Fin n → GeneralizedSliceCarrier.{u})
    (C : GeneralizedSliceCarrier.{u}) where
  region : Fin n → Set C.carrier
  region_open : ∀ i, IsOpen (region i)
  region_closed : ∀ i, IsClosed (region i)
  identify : ∀ i, SurgeryRegionEquivalence (pieces i) C Set.univ (region i)
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint (region i) (region j)
  cover : (⋃ i, region i) = Set.univ



def SmoothConnectedSumStep (A C : GeneralizedSliceCarrier.{u}) : Prop :=
  ∃ B D : GeneralizedSliceCarrier.{u},
    Nonempty (SmoothDisjointUnionData ![B, D] A) ∧
      Nonempty (SmoothConnectedSumData B D C)

structure SmoothFiniteConnectedSumAssembly {n : ℕ}
    (pieces : Fin n → GeneralizedSliceCarrier.{u})
    (C : GeneralizedSliceCarrier.{u}) where
  initial : GeneralizedSliceCarrier.{u}
  disjoint_union : SmoothDisjointUnionData pieces initial
  operations : Relation.ReflTransGen SmoothConnectedSumStep initial C



structure SurgerySphereBundle (C : GeneralizedSliceCarrier.{u}) where
  projection : C.carrier → UnitCircle
  projection_continuous : Continuous projection
  projection_surjective : Function.Surjective projection
  projection_smooth : ContMDiff (𝓡 3) (𝓡 1) ∞ projection
  local_trivialization : ∀ b : UnitCircle, ∃ U : Set UnitCircle,
    IsOpen U ∧ b ∈ U ∧
      ∃ f : C.carrier → UnitTwoSphere × UnitCircle,
      ∃ g : UnitTwoSphere × UnitCircle → C.carrier,
        f '' (projection ⁻¹' U) = Set.univ ×ˢ U ∧
        Set.LeftInvOn g f (projection ⁻¹' U) ∧
        Set.LeftInvOn f g (Set.univ ×ˢ U) ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ f (projection ⁻¹' U) ∧
        ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ g (Set.univ ×ˢ U) ∧
        ∀ x ∈ projection ⁻¹' U, (f x).2 = projection x

structure SurgeryPositiveSpaceform (C : GeneralizedSliceCarrier.{u}) where
  metric : RiemannianMetric 3 C.carrier
  connection : LeviCivitaData metric
  compact : IsCompact (Set.univ : Set C.carrier)
  connected : IsConnected (Set.univ : Set C.carrier)
  round : ConstantPositiveSectionalCurvature metric connection

inductive SurgerySummandKind
  | survivor
  | sphereBundle
  | spaceform
deriving DecidableEq




structure SurgeryTopologyConclusion (A B : GeneralizedSliceCarrier.{u}) where
  piece_count : ℕ
  piece : Fin piece_count → GeneralizedSliceCarrier.{u}
  piece_compact : ∀ i, IsCompact (Set.univ : Set (piece i).carrier)
  piece_connected : ∀ i, IsConnected (Set.univ : Set (piece i).carrier)
  kind : Fin piece_count → SurgerySummandKind
  survivor_region : Fin piece_count → Set B.carrier
  survivor : ∀ i, kind i = .survivor →
    SurgeryRegionEquivalence (piece i) B Set.univ (survivor_region i)
  survivor_component : ∀ i, kind i = .survivor →
    ∃ x : B.carrier, survivor_region i = connectedComponent x
  survivor_cover : (⋃ i : {i // kind i = .survivor}, survivor_region i.1) = Set.univ
  survivor_disjoint : ∀ i j, i ≠ j → kind i = .survivor → kind j = .survivor →
    Disjoint (survivor_region i) (survivor_region j)
  bundles : ∀ i, kind i = .sphereBundle → Nonempty (SurgerySphereBundle (piece i))
  spaceforms : ∀ i, kind i = .spaceform → Nonempty (SurgeryPositiveSpaceform (piece i))
  reconstruction : SmoothFiniteConnectedSumAssembly piece A

end PoincareConjecture
