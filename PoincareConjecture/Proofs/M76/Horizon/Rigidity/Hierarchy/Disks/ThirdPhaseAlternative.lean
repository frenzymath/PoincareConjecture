import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdPhaseDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.OriginalMarkedSphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Geometry.InteriorBall











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_third_phase_disk_or_interior_ball
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R S : Set X0} (hI : IsPLIrreducible e R) (hS : IsCompact S) (hSR : S ⊆ R)
    {c alpha beta d a b : ℝ}
    (halpha : c < alpha) (hbeta : beta < c + p)
    (ha : d < a) (hb : b < d + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : S ⊆ hamiltonZeroThirdCircleMap phi ⁻¹' {theta})
    (hconn : IsPathConnected S)
    (hinj : ∀ x : S, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x))
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X0 V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source (frontier R)) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0)) :
    (∃ (H : D ≃ₜ S) (j : V2 → X0), PolyhedralPLInCharts e j D ∧
      Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D R ∧
      (∀ z : D, j z = (H z : X0)) ∧ j '' D = S ∧
      ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) ∨
    (Disjoint S (frontier R) ∧ Nonempty (ChartwisePLSphere e S) ∧
      ∃ A : Set X0, IsCompact A ∧ A ⊆ interior R ∧
        Nonempty (ChartwisePLBall e A S)) := by
  classical
  by_cases hboundary : (S ∩ frontier R).Nonempty
  · exact Or.inl (exists_hamiltonZero_third_phase_disk e phi F hI.1 hS hSR
      halpha hbeta ha hb hfirst hsecond theta hthird hconn hinj hboundary hlocal)
  · let : T2Space X0 :=
      (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
    let : SimplyConnectedSpace S := isSimplyConnected_hamiltonZeroThirdPhase
      phi F halpha hbeta ha hb (hSR.trans hfirst) (hSR.trans hsecond)
      theta hthird hconn hinj
    have hrim : Disjoint S (frontier R) := disjoint_left.mpr
      (fun x hx hxF => hboundary ⟨x, hx, hxF⟩)
    have hSint : S ⊆ interior R := by
      intro x hx
      by_contra hn
      apply disjoint_left.mp hrim hx
      rw [hI.1.closed.frontier_eq]
      exact ⟨hSR hx, hn⟩
    have hsphere := exists_original_simplyConnected_marked_sphere
      e isCompact_hamiltonZeroAmbient hI.1 hS hlocal hrim
    exact Or.inr ⟨hrim, hsphere, hI.exists_compact_ball_subset_interior hSint hsphere⟩

end PoincareConjecture.M76
