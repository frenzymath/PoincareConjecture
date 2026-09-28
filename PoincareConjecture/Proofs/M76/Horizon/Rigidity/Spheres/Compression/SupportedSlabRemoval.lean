import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.PhaseModelExcision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.SupportedSlabDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalSupportedBallPhaseHomotopy

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < p) := ⟨by norm_num⟩

theorem ChartwisePLMap.exists_hamiltonZero_supported_slab_removal {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    {Nlower Nupper : Set X0}
    (lower : FrontierResidualModel e Nlower (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}))
    (upper : FrontierResidualModel e Nupper (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}))
    {D S : Set X0} (ball : ChartwisePLBall e D S) (theta : ℝ)
    (haTheta : (a : C0) ≠ (theta : C0)) (hbTheta : (b : C0) ≠ (theta : C0))
    (hphase : ∀ x ∈ S, (Q0 (hamiltonZeroAmbientMap phi x)).2 = (theta : C0)) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
        hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} ∧
      ∃ (lowerNew : FrontierResidualModel e Nlower (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}))
        (upperNew : FrontierResidualModel e Nupper (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)})),
        lowerNew.complexity ≤ lower.complexity ∧ upperNew.complexity ≤ upper.complexity ∧
        lowerNew.count ≤ lower.count ∧ upperNew.count ≤ upper.count ∧
        ((hamiltonZeroCircleMap phi ⁻¹' {(a : C0)} ∩ D).Nonempty → lowerNew.count < lower.count) ∧
        ((hamiltonZeroCircleMap phi ⁻¹' {(b : C0)} ∩ D).Nonempty → upperNew.count < upper.count) := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨G, hzero, houter, hone, _, hpreimage, hPL, hhom, ⟨Fnew⟩⟩ :=
    hphi.exists_hamiltonZero_supported_ball_phase_homotopy hd F ball theta hphase
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap g
  have hq (x : X0) : hamiltonZeroCircleMap psi x = (Q0 (G (1, x))).2 := by
    change (Q0 (hamiltonZeroAmbientMap (hamiltonZeroHandleMap g) x)).2 = _
    rw [hamiltonZeroAmbientMap_handle]
    rfl
  have hqD (x : X0) (hx : x ∈ D) : hamiltonZeroCircleMap psi x = (theta : C0) := by
    rw [hq, hone x hx, hamiltonZeroTargetPhaseRetraction_coordinates]
  have hqeq : EqOn (hamiltonZeroCircleMap psi) (hamiltonZeroCircleMap phi) Dᶜ := by
    intro x hx
    rw [hq, houter 1 x (fun hi => hx (interior_subset hi))]
    rfl
  have hAfront := AddCircle.frontier_closedIntervalArc p ha hab.le hb
  have havoid : Disjoint (hamiltonZeroCircleMap psi ⁻¹' frontier (AddCircle.closedIntervalArc p a b)) D := by
    rw [hAfront]
    apply Set.disjoint_left.mpr
    intro x hx hxD
    change hamiltonZeroCircleMap psi x = (a : C0) ∨ hamiltonZeroCircleMap psi x = (b : C0) at hx
    rw [hqD x hxD] at hx
    exact hx.elim (fun h => haTheta h.symm) (fun h => hbTheta h.symm)
  obtain ⟨hedomain, hefront⟩ := he.preimage_of_eq_off_closed
    (hamiltonZeroCircleMap phi) (hamiltonZeroCircleMap psi)
    (AddCircle.isCompact_closedIntervalArc p a b).isClosed
    (hfront.trans (congrArg (fun Z => hamiltonZeroCircleMap phi ⁻¹' Z) hAfront.symm))
    ball.isCompact.isClosed hqeq havoid
  rw [hAfront] at hefront
  have hlevel (c : C0) (hc : c ≠ (theta : C0)) :
      hamiltonZeroCircleMap psi ⁻¹' {c} = (hamiltonZeroCircleMap phi ⁻¹' {c}) \ interior D := by
    have hqfun : (hamiltonZeroCircleMap psi : X0 → C0) = fun x => (Q0 (G (1, x))).2 := funext hq
    rw [hqfun]
    exact hpreimage c hc
  have hphasefront (c : C0) (hc : c ≠ (theta : C0)) :
      Disjoint (hamiltonZeroCircleMap phi ⁻¹' {c}) (frontier D) := by
    rw [ball.frontier_eq]
    apply Set.disjoint_left.mpr
    intro x hx hxS
    exact hc (hx.symm.trans (hphase x hxS))
  have hnonempty (c : C0) (hc : c ≠ (theta : C0)) :
      ((hamiltonZeroCircleMap phi ⁻¹' {c}) \ interior D).Nonempty := by
    rw [← hlevel c hc]
    obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap psi Fnew c
    exact ⟨x, hx⟩
  have hlower := lower.exists_model_after_closed_excision ball.isCompact.isClosed
    (hphasefront (a : C0) haTheta) (hnonempty (a : C0) haTheta)
  have hupper := upper.exists_model_after_closed_excision ball.isCompact.isClosed
    (hphasefront (b : C0) hbTheta) (hnonempty (b : C0) hbTheta)
  rw [← hlevel (a : C0) haTheta] at hlower
  rw [← hlevel (b : C0) hbTheta] at hupper
  obtain ⟨lowerNew, hlowComplexity, hlowCount, hlowStrict⟩ := hlower
  obtain ⟨upperNew, hupComplexity, hupCount, hupStrict⟩ := hupper
  exact ⟨psi, hPL, hhom, ⟨Fnew⟩, hedomain, hefront, lowerNew, upperNew,
    hlowComplexity, hupComplexity, hlowCount, hupCount, hlowStrict, hupStrict⟩

end PoincareConjecture.M76
