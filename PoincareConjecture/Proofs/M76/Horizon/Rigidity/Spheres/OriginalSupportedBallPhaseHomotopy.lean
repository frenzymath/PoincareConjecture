import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalBallPhaseHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalPhaseSelectionPL












set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩




theorem ChartwisePLMap.exists_hamiltonZero_supported_ball_phase_homotopy {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {D S : Set X0} (b : ChartwisePLBall e D S) (theta : ℝ)
    (hphase : ∀ x ∈ S, (Q0 (hamiltonZeroAmbientMap phi x)).2 = (theta : C0)) :
    ∃ G : C(unitInterval × X0, X0),
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ interior D →
        G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ x ∈ D, G (1, x) = hamiltonZeroTargetPhaseRetraction theta
        (hamiltonZeroAmbientMap phi x)) ∧
      PolyhedralPLInCharts d (fun z => G (1, b.map z)) (closedBall (0 : V3) 1) ∧
      (∀ c : C0, c ≠ (theta : C0) →
        (fun x => (Q0 (G (1, x))).2) ⁻¹' {c} =
          (hamiltonZeroCircleMap phi ⁻¹' {c}) \ interior D) ∧
      let g : C(X0, X0) := ⟨fun x => G (1, x),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      ChartwisePLMap e d
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap g)) ∧
        Nonempty (phi.HomotopyRel (hamiltonZeroHandleMap g) B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel (hamiltonZeroHandleMap g) B0) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨hPL, l, H, hl, hlS, hformula⟩ :=
    hphi.exists_hamiltonZero_ball_phase_homotopy hd b theta hphase
  let outer : C(unitInterval × X0, X0) :=
    (hamiltonZeroAmbientMap phi).comp ⟨Prod.snd, continuous_snd⟩
  obtain ⟨G, hGin, hGout⟩ := ContinuousMap.exists_paste_of_eq_on_frontier
    b.isCompact.isClosed H.toHomotopy.toContinuousMap outer (by
      intro t x hx
      rw [b.frontier_eq] at hx
      exact H.eq_fst t hx)
  have hzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := by
    by_cases hx : x ∈ D
    · exact (hGin 0 ⟨x, hx⟩).trans (H.apply_zero ⟨x, hx⟩)
    · exact hGout 0 x (fun hi => hx (interior_subset hi))
  have hone (x : X0) (hx : x ∈ D) :
      G (1, x) = hamiltonZeroTargetPhaseRetraction theta (hamiltonZeroAmbientMap phi x) :=
    (hGin 1 ⟨x, hx⟩).trans (H.apply_one ⟨x, hx⟩)
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hgPL : ChartwisePLMap e d
      (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap g)) := by
    rw [hamiltonZeroHandleMap_domain]
    apply chartwisePL_hamiltonZero_of_phase_selection hd hphi theta g
    intro x
    by_cases hx : x ∈ D
    · exact Or.inr (hone x hx)
    · exact Or.inl (hGout 1 x (fun hi => hx (interior_subset hi)))
  refine ⟨G, hzero, hGout, hone, ?_, ?_,
    hgPL, ⟨hamiltonZeroHandleHomotopy phi G hzero⟩,
    ⟨F.trans (hamiltonZeroHandleHomotopy phi G hzero)⟩⟩
  · apply hPL.congr
    intro z hz
    exact (hone (b.map z) (b.image_closedBall.subset ⟨z, hz, rfl⟩)).symm
  · intro c hc
    ext x
    by_cases hx : x ∈ interior D
    · have hnormal : (Q0 (G (1, x))).2 = (theta : C0) := by
        rw [hone x (interior_subset hx), hamiltonZeroTargetPhaseRetraction_coordinates]
      simp only [mem_preimage, mem_singleton_iff, hnormal, hc.symm, mem_sdiff, hx, not_true_eq_false,
        and_false]
    · change (Q0 (G (1, x))).2 = c ↔ hamiltonZeroCircleMap phi x = c ∧ x ∉ interior D
      rw [hGout 1 x hx]
      exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

end PoincareConjecture.M76
