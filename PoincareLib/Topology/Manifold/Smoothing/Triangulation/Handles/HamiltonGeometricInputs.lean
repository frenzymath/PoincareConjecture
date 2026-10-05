import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.PolyhedralPLInCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffineGroupoid
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.UnitBallPairs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Compactness.Paracompact

/-!
# Concrete geometric inputs to Hamilton's lower handles

These definitions retain actual charts, boundary sets, sphere and ball
maps, and the compact-set quantifiers in the end condition. They assert
no existence theorem and no reduction to overlap straightening. Brown's
conclusion is deliberately topological; Wall's conclusion is a marked
PL compact core with one new sphere. See Hamilton 1976, pp. 64--67 and
M76 derivations 318--320.
-/

set_option autoImplicit false

universe u v

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- A closed domain in an actual compatible ambient PL atlas, with
compatible full halfspace charts along its whole ambient frontier.
The slope-one witness excludes a degenerate affine halfspace.
See Hamilton Lemma 2 and M76 derivation 320. -/
structure PLDomain (e : ι → OpenPartialHomeomorph X V3) (R : Set X) : Prop where
  cover : ∀ x : X, ∃ i, x ∈ (e i).source
  compatible : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3
  closed : IsClosed R
  halfspace : ∀ x ∈ frontier R,
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)

/-- An actual embedded PL sphere in the specified ambient chart family.
The complete cube-sphere parametrisation agrees with the map carrying
the local finite polyhedral coordinate certificates. See derivation 320. -/
structure ChartwisePLSphere (e : ι → OpenPartialHomeomorph X V3) (S : Set X) where
  parametrization : sphere (0 : V3) 1 ≃ₜ S
  map : V3 → X
  map_eq : ∀ x : sphere (0 : V3) 1, map x = (parametrization x : X)
  piecewiseAffine : PolyhedralPLInCharts e map (sphere (0 : V3) 1)

/-- A PL parametrised ball with its exact specified boundary. The
homeomorphism and chartwise finite PL map have identical values on the
whole closed cube, and boundary membership is retained both ways.
See Hamilton pp. 66--67 and M76 derivation 320. -/
structure ChartwisePLBall (e : ι → OpenPartialHomeomorph X V3) (D S : Set X) where
  boundary_subset : S ⊆ D
  parametrization : closedBall (0 : V3) 1 ≃ₜ D
  map : V3 → X
  map_eq : ∀ x : closedBall (0 : V3) 1, map x = (parametrization x : X)
  piecewiseAffine : PolyhedralPLInCharts e map (closedBall (0 : V3) 1)
  boundary_eq : ∀ x : closedBall (0 : V3) 1,
    (parametrization x : X) ∈ S ↔ (x : V3) ∈ sphere (0 : V3) 1

/-- Topological local flatness of an actual sphere in standard R^3.
The flattening charts are topological pair charts; they have no PL
regularity assumption. See Brown's input in Hamilton p. 66 and
M76 derivation 320. -/
structure LocallyFlatTopologicalSphere (S : Set V3) where
  parametrization : sphere (0 : V3) 1 ≃ₜ S
  flatten : ∀ x ∈ S, ∃ B : OpenPartialHomeomorph V3 V3,
    x ∈ B.source ∧ ∀ y ∈ B.source, y ∈ S ↔ B y 0 = 0

/-- Brown's geometric sphere-ball input in standard R^3. Its ball-pair
conclusion is topological, with the full original sphere as boundary;
it makes no claim of PL regularity of the ball map. See Hamilton p. 66
and M76 derivation 320. -/
def HasBrownLocallyFlatSphereBalls : Prop :=
  ∀ S : Set V3, Nonempty (LocallyFlatTopologicalSphere S) →
    ∃ D : Set V3, IsCompact D ∧ frontier D = S ∧ IsUnitBallPair V3 D S

/-- A cofinal compact-neighborhood formulation of one simply connected
end. Loops outside the larger compact set contract outside the original
one; the larger compact complement is connected and nonempty. No
complement is assumed itself simply connected. See Hamilton Lemma 2
and the concrete end discussion in M76 derivations 318 and 320. -/
def HasOneSimplyConnectedEnd (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ C : Set Y, IsCompact C →
    ∃ D : Set Y, IsCompact D ∧ C ⊆ interior D ∧ IsConnected Dᶜ ∧
      ∀ (x : Y) (p : Path x x), (∀ t, p t ∉ D) →
        ∃ H : p.Homotopy (Path.refl x), ∀ z, H z ∉ C

/-- Wall's compact-core input for connected domains of this actual
ambient PL atlas. The old boundary is the ambient frontier of R.
The new sphere is disjoint from it; only that sphere is the relative
frontier of K in R. The original compact set and complete old boundary
remain in the relative interior. This is an input, not an existence
proof. See Hamilton Lemma 2 and M76 derivations 318--320. -/
def HasWallCompactCore [T2Space X] [ParacompactSpace X]
    (e : ι → OpenPartialHomeomorph X V3) : Prop :=
  ∀ R : Set X, PLDomain e R → IsConnected R → IsCompact (frontier R) →
    HasOneSimplyConnectedEnd R →
      ∀ A : Set X, IsCompact A → A ⊆ R →
        ∃ K S : Set X, IsCompact K ∧ K ⊆ R ∧ PLDomain e K ∧
          S ⊆ interior R ∧ Nonempty (ChartwisePLSphere e S) ∧
          Disjoint (frontier R) S ∧ frontier K = frontier R ∪ S ∧
          (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
            interior ((Subtype.val : R → X) ⁻¹' K) ∧
          frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' S

end PoincareMT.M76
