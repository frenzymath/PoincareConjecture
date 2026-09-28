import PoincareConjecture.Definitions.M59ComponentTopology
import PoincareConjecture.Definitions.M54GroupEffects
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.GroupTheory.Coprod.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

def M59ClosedPiTwoObstructionClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    (_compact : IsCompact (Set.univ : Set M))
    (_connected : IsConnected (Set.univ : Set M)) (x : M),
    (Nonempty (FundamentalGroup M x ≃* Multiplicative ℤ) →
      Nontrivial (HomotopyGroup.Pi 2 M x)) ∧
    (∀ (G H : Type u) [Group G] [Group H] [Nontrivial G] [Nontrivial H],
      Nonempty (FundamentalGroup M x ≃* Monoid.Coprod G H) →
        Nontrivial (HomotopyGroup.Pi 2 M x))

def M59FiniteFundamentalGroupClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    (_compact : IsCompact (Set.univ : Set M))
    (_connected : IsConnected (Set.univ : Set M))
    (x : M) (_pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 M x))
    (_fundamental_type : IsFiniteFreeProductCyclic (FundamentalGroup M x)),
    Finite (FundamentalGroup M x)

def M59ClosedFiniteCoverClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    (_compact : IsCompact (Set.univ : Set M))
    (_connected : IsConnected (Set.univ : Set M))
    (x : M) (_finite : Finite (FundamentalGroup M x)),
    Nonempty (M59PointedFiniteSmoothUniversalCover x)

def M59NoncompactContractibilityClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    [SimplyConnectedSpace M]
    (_noncompact : ¬ IsCompact (Set.univ : Set M))
    (x : M) (_pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 M x)),
    ContractibleSpace M

end PoincareConjecture
