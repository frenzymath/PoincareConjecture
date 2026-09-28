import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.RelativeArcLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Maps.TargetPhaseSelection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalBallPhaseHomotopy











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Q" => hamiltonOneHierarchyCoordinates

private instance period_positive : Fact (0 < p) := ⟨by norm_num⟩



theorem exists_ball_phase_clamp {ι : Type*}
    {e : ι → OpenPartialHomeomorph X V3} {D S : Set X}
    (b : ChartwisePLBall e D S) (u : C(D, H))
    (boundary : C({x : D | (x : X) ∈ S}, ℝ))
    (hboundary : ∀ x : {x : D | (x : X) ∈ S},
      (boundary x : C) = (Q (u x)).2)
    (lower upper : ℝ) (horder : lower ≤ upper)
    (hboundaryRange : ∀ x, boundary x ∈ Icc lower upper) :
    ∃ (v : C(D, H)) (T : u.HomotopyRel v {x : D | (x : X) ∈ S}),
      (∀ (t : unitInterval) (x : D), (Q (T (t, x))).1 = (Q (u x)).1) ∧
      (∀ x : D, v x = u x ∨ v x = handlePhaseRetraction lower (u x) ∨
        v x = handlePhaseRetraction upper (u x)) ∧
      ∀ x : D, (Q (v x)).2 ∈ ((↑) : ℝ → C) '' Icc lower upper := by
  let : ContractibleSpace D := b.contractibleSpace
  let : LocallyPathConnectedSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace D :=
    b.parametrization.symm.isOpenEmbedding.locallyPathConnectedSpace
  let f : C(D, C) := ⟨fun x => (Q (u x)).2,
    continuous_snd.comp ((Q).continuous.comp u.continuous)⟩
  obtain ⟨lift, endpoint, W, hlift, _, hendpoint, hrange, _⟩ :=
    AddCircle.exists_homotopyRel_clamped_lift_of_connected_set p f
      b.isConnected_boundary_in_carrier boundary hboundary lower upper horder hboundaryRange
  let v : C(D, H) := ⟨fun x => (Q).symm ((Q (u x)).1, endpoint x),
    (Q).symm.continuous.comp
      ((continuous_fst.comp ((Q).continuous.comp u.continuous)).prodMk endpoint.continuous)⟩
  let T : u.HomotopyRel v {x : D | (x : X) ∈ S} := {
    toFun := fun z => (Q).symm ((Q (u z.2)).1, W z)
    continuous_toFun := (Q).symm.continuous.comp
      ((continuous_fst.comp ((Q).continuous.comp
        (u.continuous.comp continuous_snd))).prodMk W.continuous_toFun)
    map_zero_left := by
      intro x
      rw [W.apply_zero]
      exact (Q).symm_apply_apply (u x)
    map_one_left := by intro x; rw [W.apply_one]; rfl
    prop' := by
      intro t x hx
      change (Q).symm ((Q (u x)).1, W (t, x)) = u x
      rw [W.eq_fst t hx]
      exact (Q).symm_apply_apply (u x) }
  have hv (x : D) : Q (v x) = ((Q (u x)).1, endpoint x) :=
    (Q).apply_symm_apply _
  refine ⟨v, T, ?_, ?_, ?_⟩
  · intro t x
    change (Q ((Q).symm ((Q (u x)).1, W (t, x)))).1 = _
    rw [(Q).apply_symm_apply]
  · intro x
    by_cases hlow : lift x ≤ lower
    · right; left
      apply (Q).injective
      rw [hv, handlePhaseRetraction_coordinates, hendpoint,
        projIcc_of_le_left horder hlow]
    · by_cases hupp : upper ≤ lift x
      · right; right
        apply (Q).injective
        rw [hv, handlePhaseRetraction_coordinates, hendpoint,
          projIcc_of_right_le horder hupp]
      · left
        apply (Q).injective
        rw [hv, hendpoint, projIcc_of_mem horder
          ⟨(lt_of_not_ge hlow).le, (lt_of_not_ge hupp).le⟩, hlift]
        rfl
  · intro x
    rw [hv]
    exact hrange ⟨x, rfl⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
