import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic
import Mathlib.Logic.Relation

/-! Adapted from Mapher `PoincareMT/Definitions/Ch15/SurgeryTopology.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/


set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology
universe u
namespace PoincareMT

/-- A parametrized embedded ball with a smooth collar outside its boundary. -/
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

/-- The smooth collar supplies the gluing structure at the central sphere;
the two complements already have their original smooth structures. -/
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

/-- One connected sum between two components of a possibly disconnected
manifold. The decomposition into two open-and-closed pieces is explicit. -/
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


end PoincareMT
