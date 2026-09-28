import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Compactness.Paracompact

set_option autoImplicit false

universe u v

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

structure PLDomain (e : ι → OpenPartialHomeomorph X V3) (R : Set X) : Prop where
  cover : ∀ x : X, ∃ i, x ∈ (e i).source
  compatible : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3
  closed : IsClosed R
  halfspace : ∀ x ∈ frontier R,
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)

structure ChartwisePLSphere (e : ι → OpenPartialHomeomorph X V3) (S : Set X) where
  parametrization : sphere (0 : V3) 1 ≃ₜ S
  map : V3 → X
  map_eq : ∀ x : sphere (0 : V3) 1, map x = (parametrization x : X)
  piecewiseAffine : PolyhedralPLInCharts e map (sphere (0 : V3) 1)

structure ChartwisePLBall (e : ι → OpenPartialHomeomorph X V3) (D S : Set X) where
  boundary_subset : S ⊆ D
  parametrization : closedBall (0 : V3) 1 ≃ₜ D
  map : V3 → X
  map_eq : ∀ x : closedBall (0 : V3) 1, map x = (parametrization x : X)
  piecewiseAffine : PolyhedralPLInCharts e map (closedBall (0 : V3) 1)
  boundary_eq : ∀ x : closedBall (0 : V3) 1,
    (parametrization x : X) ∈ S ↔ (x : V3) ∈ sphere (0 : V3) 1

structure LocallyFlatTopologicalSphere (S : Set V3) where
  parametrization : sphere (0 : V3) 1 ≃ₜ S
  flatten : ∀ x ∈ S, ∃ B : OpenPartialHomeomorph V3 V3,
    x ∈ B.source ∧ ∀ y ∈ B.source, y ∈ S ↔ B y 0 = 0

def HasBrownLocallyFlatSphereBalls : Prop :=
  ∀ S : Set V3, Nonempty (LocallyFlatTopologicalSphere S) →
    ∃ D : Set V3, IsCompact D ∧ frontier D = S ∧ IsUnitBallPair V3 D S

def HasOneSimplyConnectedEnd (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ C : Set Y, IsCompact C →
    ∃ D : Set Y, IsCompact D ∧ C ⊆ interior D ∧ IsConnected Dᶜ ∧
      ∀ (x : Y) (p : Path x x), (∀ t, p t ∉ D) →
        ∃ H : p.Homotopy (Path.refl x), ∀ z, H z ∉ C

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

end PoincareConjecture.M76
