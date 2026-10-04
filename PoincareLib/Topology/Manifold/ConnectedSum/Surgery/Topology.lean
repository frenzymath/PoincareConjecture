import PoincareLib.Topology.Manifold.ConnectedSum.Basic
import PoincareLib.Geometry.RicciFlow.Soliton.Basic

/-! Adapted from Mapher `PoincareMT/Definitions/Ch15/SurgeryTopology.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# Smooth connected sums and surgery reconstruction

A connected sum is represented by two punctured manifolds and a smooth
sphere collar whose negative and positive halves agree with the two ball
coordinates. Finite reconstruction is the reflexive transitive closure of
this actual operation, starting from a finite disjoint union of summands.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- A smooth two-sphere bundle over the circle, stated using genuine local
bundle coordinates. Both orientable and nonorientable bundles are allowed. -/
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

/-- Each surviving piece is an actual component of the post-surgery slice.
All such components occur once; other pieces are the standard discarded
topological types of Proposition 15.3. -/
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

end PoincareMT
