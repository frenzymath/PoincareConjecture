import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.IncompressibleBallAvoidance
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Isotopy.Mathlib.RelativeCircleLift
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetPhaseRetractionPL
import PoincareConjecture.Proofs.M76.Rigidity.OriginalHandleHomotopy
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => closedBall (0 : V3) 1
local notation "Q3" => sphere (0 : V3) 1

theorem ChartwisePLBall.isConnected_boundary_in_carrier
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D S : Set X}
    (b : ChartwisePLBall e D S) : IsConnected {x : D | (x : X) ∈ S} := by
  have hdim : 1 < Module.finrank ℝ V3 := by simp
  have hrank : 1 < Module.rank ℝ V3 := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdim
  let : ConnectedSpace Q3 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere hrank (0 : V3) zero_le_one)
  let j : C(Q3, D) :=
    ⟨fun z => b.parametrization ⟨z, sphere_subset_closedBall z.property⟩,
      b.parametrization.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have himage : range j = {x : D | (x : X) ∈ S} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (b.boundary_eq _).mpr z.property
    · intro hx
      change (x : X) ∈ S at hx
      let z : C3 := b.parametrization.symm x
      have hz : (z : V3) ∈ Q3 := (b.boundary_eq z).mp (by
        simpa only [z, b.parametrization.apply_symm_apply] using hx)
      exact ⟨⟨z, hz⟩, b.parametrization.apply_symm_apply x⟩
  rw [← himage]
  exact isConnected_range j.continuous

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

theorem ChartwisePLMap.exists_hamiltonZero_ball_phase_homotopy {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {D S : Set X0} (b : ChartwisePLBall e D S) (theta : ℝ)
    (hphase : ∀ x ∈ S, (Q0 (hamiltonZeroAmbientMap phi x)).2 = (theta : C0)) :
    let gX := hamiltonZeroAmbientMap phi
    let u : C(D, X0) := gX.comp ⟨Subtype.val, continuous_subtype_val⟩
    PolyhedralPLInCharts d (hamiltonZeroTargetPhaseRetraction theta ∘ gX ∘ b.map) C3 ∧
      ∃ (l : C(D, ℝ))
        (H : u.HomotopyRel ((hamiltonZeroTargetPhaseRetraction theta).comp u)
          {x : D | (x : X0) ∈ S}),
        (∀ x : D, (l x : C0) = (Q0 (gX x)).2) ∧
        (∀ x : D, (x : X0) ∈ S → l x = theta) ∧
        ∀ (t : unitInterval) (x : D),
          Q0 (H (t, x)) = ((Q0 (gX x)).1,
            (((1 - (t : ℝ)) * l x + (t : ℝ) * theta : ℝ) : C0)) := by
  let : ContractibleSpace D := b.contractibleSpace
  let : LocallyPathConnectedSpace C3 := (convex_closedBall (0 : V3) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace D :=
    b.parametrization.symm.isOpenEmbedding.locallyPathConnectedSpace
  let gX := hamiltonZeroAmbientMap phi
  let u : C(D, X0) := gX.comp ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(D, C0) := ⟨fun x => (Q0 (u x)).2,
    continuous_snd.comp ((Q0).continuous.comp u.continuous)⟩
  obtain ⟨l, T, hl, hlS, hT⟩ :=
    AddCircle.exists_homotopyRel_const_of_connected_set (4 * 16) f
      b.isConnected_boundary_in_carrier theta (fun x hx => hphase x hx)
  let H : u.HomotopyRel ((hamiltonZeroTargetPhaseRetraction theta).comp u)
      {x : D | (x : X0) ∈ S} := {
    toFun := fun z => (Q0).symm ((Q0 (u z.2)).1, T z)
    continuous_toFun := (Q0).symm.continuous.comp
      ((continuous_fst.comp ((Q0).continuous.comp
        (u.continuous.comp continuous_snd))).prodMk T.continuous_toFun)
    map_zero_left := by
      intro x
      rw [T.apply_zero]
      exact (Q0).symm_apply_apply (u x)
    map_one_left := by
      intro x
      rw [T.apply_one]
      rfl
    prop' := by
      intro t x hx
      change (Q0).symm ((Q0 (u x)).1, T (t, x)) = u x
      rw [T.eq_fst t hx]
      exact (Q0).symm_apply_apply (u x) }
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKC, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3 C3 Q3)
  have hbK : PolyhedralPLInCharts e b.map K.space := by
    rw [hKC]
    exact b.piecewiseAffine
  have hg : PolyhedralPLInCharts d (gX ∘ b.map) C3 := by
    simpa only [hKC, gX, Function.comp_def] using
      hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hbK
  refine ⟨hd.polyhedralPL_hamiltonZeroTargetPhaseRetraction theta hg, l, H, hl, hlS, ?_⟩
  intro t x
  have hcoord : Q0 (H (t, x)) = ((Q0 (u x)).1, T (t, x)) :=
    (Q0).apply_symm_apply _
  rw [hcoord, hT]
  rfl

end PoincareConjecture.M76
