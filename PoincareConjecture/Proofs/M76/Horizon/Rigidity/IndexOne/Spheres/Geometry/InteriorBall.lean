import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.ClosedPhaseSphere
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem IsPLIrreducible.exists_compact_ball_subset_interior
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R S : Set X}
    (hI : IsPLIrreducible e R) (hS : S ⊆ interior R)
    (hsphere : Nonempty (ChartwisePLSphere e S)) :
    ∃ D : Set X, IsCompact D ∧ D ⊆ interior R ∧ Nonempty (ChartwisePLBall e D S) := by
  obtain ⟨D, hDR, ⟨b⟩⟩ := hI.2 S hS hsphere
  exact ⟨D, b.isCompact, b.subset_interior hDR hS, ⟨b⟩⟩

namespace HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem exists_closed_source_component_interior_ball
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x))
    {S : Set X} (hSne : S.Nonempty) (hS : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hrim : Disjoint S (frontier R)) :
    ∃ D : Set X, IsCompact D ∧ D ⊆ interior R ∧ Nonempty (ChartwisePLBall e D S) := by
  have hSint : S ⊆ interior R := by
    intro x hx
    by_contra hn
    apply disjoint_left.mp hrim hx
    rw [hI.1.closed.frontier_eq]
    exact ⟨sourceSurface_subset phi theta (hS hx), hn⟩
  exact hI.exists_compact_ball_subset_interior hSint
    (exists_closed_source_component_sphere e d phi hphi F0 heN hfront hAB hcorner
      hinj hSne hS hcomponent hrim)

end HamiltonIntervalTorus
end PoincareConjecture.M76
