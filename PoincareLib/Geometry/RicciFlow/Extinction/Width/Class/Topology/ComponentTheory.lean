import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Topology.ComponentData
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.GroupEffects
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.GroupTheory.Coprod.Basic

/-!
# M59 topology statements on primitive manifolds

These are separate conclusions of the single M59 theorem. Its outer proof
boundary receives the applied M02 topology provider once; callers of these
claims supply only the displayed manifold properties.

Morgan--Tian Claims 18.19--18.20, printed p. 431, give the group obstruction
and finite fundamental group. The finite-cover discussion there and after
Proposition 18.9, printed p. 424, gives the homotopy-sphere cover. The latter
discussion also supplies the noncompact Hurewicz--Whitehead argument.
See `reviews/contracts/M59-round1.md` for the source and errata review.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- Claim 18.20: a closed connected smooth three-manifold with infinite cyclic
fundamental group, or a free product of two nontrivial groups, has nontrivial
pi2. The groups in the two-factor obstruction need not be finite or cyclic.
Source: Morgan--Tian printed p. 431, `MT2007.txt:21129-21133`. -/
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

/-- Claims 18.19--18.20: pi2-vanishing makes a finite free product of finite
and infinite cyclic fundamental-group factors finite. Trivial factors may be
discarded; at most one nontrivial finite factor remains.
Source: Morgan--Tian printed p. 431, `MT2007.txt:21124-21140`. -/
def M59FiniteFundamentalGroupClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    (_compact : IsCompact (Set.univ : Set M))
    (_connected : IsConnected (Set.univ : Set M))
    (x : M) (_pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 M x))
    (_fundamental_type : IsFiniteFreeProductCyclic (FundamentalGroup M x)),
    Finite (FundamentalGroup M x)

/-- A closed connected smooth three-manifold with finite fundamental group
has an actual pointed finite smooth universal cover homotopy equivalent to S3.
The induced pi3 equivalence uses the covering projection. M02's chosen-point
conclusions must be transported to the specified lift during the proof.
Source: Morgan--Tian printed pp. 424 and 431,
`MT2007.txt:20792-20800,21134-21140`. -/
def M59ClosedFiniteCoverClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    (_compact : IsCompact (Set.univ : Set M))
    (_connected : IsConnected (Set.univ : Set M))
    (x : M) (_finite : Finite (FundamentalGroup M x)),
    Nonempty (M59PointedFiniteSmoothUniversalCover x)

/-- A noncompact simply connected smooth three-manifold with trivial based
pi2 is contractible. The smooth model has no boundary; Hausdorffness and
second countability are explicit. This is a homotopy conclusion, not a claim
of a homeomorphism with Euclidean space.
Source: Morgan--Tian Proposition 18.9 discussion, printed p. 424,
`MT2007.txt:20792-20800`. -/
def M59NoncompactContractibilityClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    [SimplyConnectedSpace M]
    (_noncompact : ¬ IsCompact (Set.univ : Set M))
    (x : M) (_pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 M x)),
    ContractibleSpace M

end PoincareMT
