import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.MinimalInstalledPhaseProducts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.InwardFirstPhaseCollars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.FirstFrontierCoverings
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.SelectedComponentBoundaries
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.OriginalBoundaryCandidates







set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_rigidity_or_original_failure_components {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    (∃ f : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 f) ∧
      Nonempty (phi.HomotopyRel ⟨f, f.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨f, f.continuous⟩ B0)) ∨
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      ∃ (R : Set X0) (a b : C0), a ≠ b ∧ IsCompact R ∧ IsPLIrreducible e R ∧
        IsCoveringMap (hamiltonZeroRetainedTangentialMap psi (frontier R)) ∧
        HamiltonZeroBoundaryFailureArc e R psi ∧
        ∀ x ∈ R, let P := connectedComponentIn R x
          IsCompact P ∧ IsConnected P ∧ IsPLIrreducible e P ∧
          (∀ z : P, (z : X0) ∈ frontier R ↔ (z : X0) ∈ frontier P) ∧
          ∃ (S₀ S₁ : Set X0) (hS₀ : S₀ ⊆ P) (hS₁ : S₁ ⊆ P)
            (x₀ : S₀) (x₁ : S₁),
            S₀ ⊆ frontier P ∧ S₁ ⊆ frontier P ∧ Disjoint S₀ S₁ ∧
            connectedComponentIn (frontier P) (x₀ : X0) = S₀ ∧
            connectedComponentIn (frontier P) (x₁ : X0) = S₁ ∧
            (∀ z : S₀, Nontrivial (FundamentalGroup S₀ z)) ∧
            (∀ z : S₁, Nontrivial (FundamentalGroup S₁ z)) ∧
            (∀ z : S₀, Function.Injective (FundamentalGroup.map
              (⟨Subtype.val, continuous_subtype_val⟩ : C(S₀, X0)) z)) ∧
            (∀ z : S₁, Function.Injective (FundamentalGroup.map
              (⟨Subtype.val, continuous_subtype_val⟩ : C(S₁, X0)) z)) ∧
            (∀ z ∈ S₀, hamiltonZeroCircleMap psi z = a) ∧
            (∀ z ∈ S₁, hamiltonZeroCircleMap psi z = b) ∧
            (∃ (A B : OriginalTorusEulerCandidate e P (frontier P)),
              A.surface = S₀ ∧ B.surface = S₁) ∧
            ∃ k : Path ((ContinuousMap.inclusion hS₀) x₀) ((ContinuousMap.inclusion hS₁) x₁),
              (FundamentalGroup.map (ContinuousMap.inclusion hS₀) x₀).range.Commensurable
                (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
                  (FundamentalGroup.map (ContinuousMap.inclusion hS₁) x₁)).range) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  rcases exists_hamiltonZero_minimal_installed_phase_products e d hI hd phi hphi F with
    rigidity | stage
  · exact Or.inl rigidity
  obtain ⟨n, hmin, a, ha, b, hb, psi, hpsi, ⟨Hbase⟩, ⟨Fpsi⟩,
    he, hfront, hIR, hIS, hfrontInj, hsides, _,
    ⟨Nlower, Nupper, lower, upper, hcount, hnoA, hnoB, hntA, hntB⟩,
    s, r, hr, J, c, H, g, hJ, _, hi, hzero, hopen, hg, _, hproduct, _,
    ⟨side, failure⟩⟩ := stage
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  have hne : (a : C0) ≠ (b : C0) := by
    have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith [ha.1, ha.2]
    have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith [hb.1, hb.2]
    exact fun h => hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h)
  have hK (t : Bool) : IsCompact (J t).space := (J t).isCompact_space_of_finite (hJ t)
  have hcover := isCoveringMap_hamiltonZero_first_frontiers_of_installed_products
    psi Fpsi ha0 hab hbp he hfront (fun t => (J t).space) hK hr c hi hopen H hzero g hg hproduct
  obtain ⟨r', hr', _, hinward⟩ := exists_hamiltonZero_inward_first_phase_collars
    psi ha0 hab hbp (fun t => (J t).space) hK hr c hi hopen H hzero g hg hproduct
  obtain ⟨K', c', H', g', hK', hi', hopen', hside', hphase', hg', hzero', htangent'⟩ :=
    hinward side
  let R := hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p
    (if side then b else a) (if side then a + p else b)
  have hcomp := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap psi) ha0 hab hbp hfront
  have hR : R = if side then
      (interior (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))ᶜ
      else hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b := by
    cases side
    · rfl
    · exact hcomp.symm
  have hIR' : IsPLIrreducible e R := by
    rw [hR]
    cases side
    · exact hIR
    · exact hIS
  have hinjR : ∀ z : R, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion R) z) := by
    rw [hR]
    cases side <;> exact hsides _ (by simp)
  refine Or.inr ⟨psi, hpsi, ⟨Hbase⟩, ⟨Fpsi⟩, R, a, b, hne,
    hIR'.1.closed.isCompact, hIR', hcover side, failure, ?_⟩
  intro x hx P
  obtain ⟨hPc, hPconn, hIP, hinjP, iA, iB, hAP, hBP, hdis, hAF, hBF,
    hwholeA, hwholeB, _, _, hincA, hincB, xA, xB, _, _, k, hcomm, _⟩ :=
    exists_hamiltonZero_selected_component_boundaries hI hd hpsi Hbase Fpsi ha hb he hfront
      hfrontInj lower upper hnoA hnoB hntA hntB (by simpa only [hcount] using hmin)
      side K' hK' c' hr' hi' hopen' hIR' hinjR hside' hphase' H' g' hg' hzero' htangent' x hx
  have hambA (z : lower.components iA) : Function.Injective (FundamentalGroup.map
      (VanKampen.inclusion (lower.components iA)) z) := by
    change Function.Injective (FundamentalGroup.map
      ((VanKampen.inclusion P).comp (ContinuousMap.inclusion hAP)) z)
    rw [FundamentalGroup.map_comp]
    exact (hinjP _).comp (hincA z)
  have hambB (z : upper.components iB) : Function.Injective (FundamentalGroup.map
      (VanKampen.inclusion (upper.components iB)) z) := by
    change Function.Injective (FundamentalGroup.map
      ((VanKampen.inclusion P).comp (ContinuousMap.inclusion hBP)) z)
    rw [FundamentalGroup.map_comp]
    exact (hinjP _).comp (hincB z)
  obtain ⟨A, hA⟩ := hIP.1.exists_original_torus_candidate_on_frontier e hPc hAF xA
    (hwholeA xA xA.property) (hntA iA xA) (hambA xA)
  obtain ⟨B, hB⟩ := hIP.1.exists_original_torus_candidate_on_frontier e hPc hBF xB
    (hwholeB xB xB.property) (hntB iB xB) (hambB xB)
  have hPfront : frontier P = P ∩ frontier R :=
    hIR'.1.frontier_connectedComponentIn_of_compact hIR'.1.closed.isCompact hx
  refine ⟨hPc, hPconn, hIP, ?_, lower.components iA, upper.components iB,
    hAP, hBP, xA, xB, hAF, hBF, hdis, hwholeA xA xA.property, hwholeB xB xB.property,
    hntA iA, hntB iB, hambA, hambB, ?_, ?_, ⟨A, B, hA, hB⟩, k, hcomm⟩
  · intro z
    rw [hPfront]
    exact ⟨fun h => ⟨z.property, h⟩, And.right⟩
  · exact fun z hz => (lower.component iA).2.2.1 hz
  · exact fun z hz => (upper.component iB).2.2.1 hz

end PoincareConjecture.M76
