import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.RelativeArcLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.SupportedBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_hamiltonZero_ball_second_phase_clamp
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {D S : Set X0}
    (b : ChartwisePLBall e D S) (u : C(D, X0))
    (boundary : C({x : D | (x : X0) ∈ S}, ℝ))
    (hboundary : ∀ x : {x : D | (x : X0) ∈ S},
      (boundary x : C0) = (Q0 (u x)).1.2)
    (lower upper : ℝ) (horder : lower ≤ upper)
    (hboundaryRange : ∀ x, boundary x ∈ Icc lower upper) :
    ∃ (v : C(D, X0)) (T : u.HomotopyRel v {x : D | (x : X0) ∈ S}),
      (∀ (t : unitInterval) (x : D),
        (Q0 (T (t, x))).1.1 = (Q0 (u x)).1.1 ∧ (Q0 (T (t, x))).2 = (Q0 (u x)).2) ∧
      (∀ x : D, v x = u x ∨ v x = hamiltonZeroTargetSecondPhaseRetraction lower (u x) ∨
        v x = hamiltonZeroTargetSecondPhaseRetraction upper (u x)) ∧
      ∀ x : D, (Q0 (v x)).1.2 ∈ AddCircle.closedIntervalArc p lower upper := by
  let : ContractibleSpace D := b.contractibleSpace
  let : LocallyPathConnectedSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace D :=
    b.parametrization.symm.isOpenEmbedding.locallyPathConnectedSpace
  let q : C(D, C0) := ⟨fun x => (Q0 (u x)).1.2,
    ((Q0).continuous.comp u.continuous).fst.snd⟩
  obtain ⟨lift, endpoint, W, hlift, _, hendpoint, hrange, _⟩ :=
    AddCircle.exists_homotopyRel_clamped_lift_of_connected_set p q
      b.isConnected_boundary_in_carrier boundary hboundary lower upper horder hboundaryRange
  let v : C(D, X0) := ⟨fun x => (Q0).symm (((Q0 (u x)).1.1, endpoint x), (Q0 (u x)).2),
    (Q0).symm.continuous.comp
      ((((Q0).continuous.comp u.continuous).fst.fst.prodMk endpoint.continuous).prodMk
        ((Q0).continuous.comp u.continuous).snd)⟩
  let T : u.HomotopyRel v {x : D | (x : X0) ∈ S} := {
    toFun := fun z => (Q0).symm (((Q0 (u z.2)).1.1, W z), (Q0 (u z.2)).2)
    continuous_toFun := (Q0).symm.continuous.comp
      ((((Q0).continuous.comp (u.continuous.comp continuous_snd)).fst.fst.prodMk
        W.continuous_toFun).prodMk
          ((Q0).continuous.comp (u.continuous.comp continuous_snd)).snd)
    map_zero_left := by
      intro x
      rw [W.apply_zero]
      exact (Q0).symm_apply_apply (u x)
    map_one_left := by intro x; rw [W.apply_one]; rfl
    prop' := by
      intro t x hx
      change (Q0).symm (((Q0 (u x)).1.1, W (t, x)), (Q0 (u x)).2) = u x
      rw [W.eq_fst t hx]
      exact (Q0).symm_apply_apply (u x) }
  have hv (x : D) : Q0 (v x) = (((Q0 (u x)).1.1, endpoint x), (Q0 (u x)).2) :=
    (Q0).apply_symm_apply _
  refine ⟨v, T, ?_, ?_, ?_⟩
  · intro t x
    change (Q0 ((Q0).symm (((Q0 (u x)).1.1, W (t, x)), (Q0 (u x)).2))).1.1 = _ ∧
      (Q0 ((Q0).symm (((Q0 (u x)).1.1, W (t, x)), (Q0 (u x)).2))).2 = _
    rw [(Q0).apply_symm_apply]
    exact ⟨rfl, rfl⟩
  · intro x
    by_cases hlow : lift x ≤ lower
    · right; left
      apply (Q0).injective
      rw [hv, hamiltonZeroTargetSecondPhaseRetraction_coordinates, hendpoint,
        projIcc_of_le_left horder hlow]
    · by_cases hupp : upper ≤ lift x
      · right; right
        apply (Q0).injective
        rw [hv, hamiltonZeroTargetSecondPhaseRetraction_coordinates, hendpoint,
          projIcc_of_right_le horder hupp]
      · left
        apply (Q0).injective
        rw [hv, hendpoint, projIcc_of_mem horder
          ⟨(lt_of_not_ge hlow).le, (lt_of_not_ge hupp).le⟩, hlift]
        rfl
  · intro x
    rw [hv]
    exact hrange ⟨x, rfl⟩

theorem exists_hamiltonZero_supported_ball_second_phase_clamp
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {D S : Set X0}
    (b : ChartwisePLBall e D S) (f : C(X0, X0))
    (boundary : C({x : D | (x : X0) ∈ S}, ℝ))
    (hboundary : ∀ x : {x : D | (x : X0) ∈ S},
      (boundary x : C0) = (Q0 (f x)).1.2)
    (lower upper : ℝ) (horder : lower ≤ upper)
    (hboundaryRange : ∀ x, boundary x ∈ Icc lower upper) :
    ∃ (g : C(X0, X0)) (T : f.HomotopyRel g (interior D)ᶜ),
      (∀ (t : unitInterval) (x : X0),
        (Q0 (T (t, x))).1.1 = (Q0 (f x)).1.1 ∧ (Q0 (T (t, x))).2 = (Q0 (f x)).2) ∧
      (∀ x : X0, g x = f x ∨ g x = hamiltonZeroTargetSecondPhaseRetraction lower (f x) ∨
        g x = hamiltonZeroTargetSecondPhaseRetraction upper (f x)) ∧
      ∀ x ∈ D, (Q0 (g x)).1.2 ∈ AddCircle.closedIntervalArc p lower upper := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let u : C(D, X0) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨v, W, hWcoord, hvchoice, hvrange⟩ :=
    exists_hamiltonZero_ball_second_phase_clamp b u boundary hboundary
      lower upper horder hboundaryRange
  let outer : C(unitInterval × X0, X0) := f.comp ⟨Prod.snd, continuous_snd⟩
  obtain ⟨G, hGin, hGout⟩ := ContinuousMap.exists_paste_of_eq_on_frontier
    b.isCompact.isClosed W.toHomotopy.toContinuousMap outer (by
      intro t x hx
      have hxS : (x : X0) ∈ S := by rwa [b.frontier_eq] at hx
      exact W.eq_fst t hxS)
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hzero (x : X0) : G (0, x) = f x := by
    by_cases hx : x ∈ D
    · exact (hGin 0 ⟨x, hx⟩).trans (W.apply_zero ⟨x, hx⟩)
    · exact hGout 0 x (fun h => hx (interior_subset h))
  let T : f.HomotopyRel g (interior D)ᶜ := {
    toFun := G
    continuous_toFun := G.continuous
    map_zero_left := hzero
    map_one_left := fun _ => rfl
    prop' := fun t x hx => hGout t x hx }
  have hg (x : D) : g x = v x := (hGin 1 x).trans (W.apply_one x)
  refine ⟨g, T, ?_, ?_, ?_⟩
  · intro t x
    change (Q0 (G (t, x))).1.1 = _ ∧ (Q0 (G (t, x))).2 = _
    by_cases hx : x ∈ D
    · rw [hGin t ⟨x, hx⟩]
      exact hWcoord t ⟨x, hx⟩
    · rw [hGout t x (fun h => hx (interior_subset h))]
      exact ⟨rfl, rfl⟩
  · intro x
    by_cases hx : x ∈ D
    · rw [hg ⟨x, hx⟩]
      exact hvchoice ⟨x, hx⟩
    · exact Or.inl (hGout 1 x (fun h => hx (interior_subset h)))
  · intro x hx
    rw [hg ⟨x, hx⟩]
    exact hvrange ⟨x, hx⟩

end PoincareConjecture.M76
