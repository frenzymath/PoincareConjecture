import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.ArcHomotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.ArcSelection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.ClosedArcBoundaryLift









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem ChartwisePLMap.exists_hamiltonZero_original_ball_arc_removal
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {D S : Set X0} (b : ChartwisePLBall e D S)
    (lower upper : ℝ) (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < p)
    (hboundary : ∀ x ∈ S, hamiltonZeroSecondCircleMap phi x ∈
      AddCircle.closedIntervalArc p lower upper) :
    ∃ (psi : C(H0, H0)) (G : C(unitInterval × X0, X0)),
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ x, G (1, x) = hamiltonZeroAmbientMap psi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ interior D →
        G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).1.1 = (Q0 (hamiltonZeroAmbientMap phi x)).1.1) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x ∈ D, hamiltonZeroSecondCircleMap psi x ∈
        AddCircle.closedIntervalArc p lower upper) ∧
      (∀ c : C0, c ∉ AddCircle.closedIntervalArc p lower upper →
        (hamiltonZeroSecondCircleMap psi ⁻¹' {c}) =
          (hamiltonZeroSecondCircleMap phi ⁻¹' {c}) \ D) := by
  let f := hamiltonZeroAmbientMap phi
  let q : C({x : D | (x : X0) ∈ S}, C0) :=
    ⟨fun x => hamiltonZeroSecondCircleMap phi x,
      (hamiltonZeroSecondCircleMap phi).continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)⟩
  obtain ⟨boundary, hboundaryLift, hboundaryRange⟩ :=
    AddCircle.exists_lift_in_closed_arc p q lower upper hlower hupper
      (fun x => hboundary x x.property)
  obtain ⟨g, T, hcoord, hchoice, hrange⟩ :=
    exists_hamiltonZero_supported_ball_second_phase_clamp b f boundary
      (by intro x; simpa only [q, ContinuousMap.coe_mk,
        hamiltonZeroSecondCircleMap_ambient] using hboundaryLift x)
      lower upper horder hboundaryRange
  let psi := hamiltonZeroHandleMap g
  let G := T.toHomotopy.toContinuousMap
  have hzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := T.apply_zero x
  have hend : (⟨fun x => G (1, x),
      G.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(X0, X0)) = g := by
    exact ContinuousMap.ext (fun x => T.apply_one x)
  have hH : Nonempty (phi.HomotopyRel psi B0) := by
    have H := hamiltonZeroHandleHomotopy phi G hzero
    rw [hend] at H
    exact ⟨H⟩
  have hone (x : X0) : G (1, x) = hamiltonZeroAmbientMap psi x := by
    rw [hamiltonZeroAmbientMap_handle]
    exact T.apply_one x
  have hq2 (x : X0) : hamiltonZeroSecondCircleMap psi x = (Q0 (g x)).1.2 := by
    rw [hamiltonZeroSecondCircleMap_ambient, hamiltonZeroAmbientMap_handle]
  have hfixed (x : X0) (hx : x ∉ interior D) :
      hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x := by
    rw [← hone]
    exact T.eq_fst 1 hx
  refine ⟨psi, G, hzero, hone, fun t x hx => T.eq_fst t hx, ?_,
    fun t x => (hcoord t x).1, ?_, hH, ⟨F.trans hH.some⟩, ?_, ?_, ?_⟩
  · intro t x
    rw [← hamiltonZeroAmbientMap_circle]
    exact (hcoord t x).2
  · rw [hamiltonZeroHandleMap_domain]
    exact hphi.hamiltonZero_second_phase_selection hd lower upper g hchoice
  · apply ContinuousMap.ext
    intro x
    rw [← hamiltonZeroAmbientMap_circle, ← hamiltonZeroAmbientMap_circle,
      hamiltonZeroAmbientMap_handle]
    simpa only [T.apply_one] using (hcoord 1 x).2
  · intro x hx
    rw [hq2]
    exact hrange x hx
  · intro c hc
    ext x
    by_cases hx : x ∈ D
    · have hnew : hamiltonZeroSecondCircleMap psi x ≠ c := by
        intro h
        exact hc (h ▸ (hq2 x ▸ hrange x hx))
      simp only [mem_preimage, mem_singleton_iff, hnew, mem_sdiff, hx,
        not_true_eq_false, and_false]
    · have heq : hamiltonZeroSecondCircleMap psi x = hamiltonZeroSecondCircleMap phi x := by
        rw [hamiltonZeroSecondCircleMap_ambient, hamiltonZeroSecondCircleMap_ambient,
          hfixed x (fun hi => hx (interior_subset hi))]
      simp only [mem_preimage, mem_singleton_iff, heq, mem_sdiff, hx,
        not_false_eq_true, and_true]

end PoincareConjecture.M76
