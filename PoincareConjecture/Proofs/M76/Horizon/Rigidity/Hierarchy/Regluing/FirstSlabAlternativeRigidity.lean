import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.FirstSlabDiskAlternatives
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.FirstSlabRigidity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.SourceTerminalBallRigidity











set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_rigidity_or_first_boundary_failure
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {alpha beta : ℝ} (ha : 0 < alpha) (hab : alpha < beta) (hb : beta < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta) =
      hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (hI : ∀ side : Bool, IsPLIrreducible e (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)))
    (hinj : ∀ side : Bool, ∀ x : (hamiltonZeroCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then beta else alpha) (if side then alpha + p else beta)),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(_, X0)) x))
    (K : Bool → Set E) (hK : ∀ s, IsCompact (K s))
    {rho : ℝ} (hrho : 0 < rho) (c : Bool → E × ℝ → X0)
    (hi : ∀ s, IsEmbedding (fun z : (K s ×ˢ Icc (-rho) rho : Set (E × ℝ)) => c s z))
    (hopen : ∀ s eps, 0 < eps → eps ≤ rho → IsOpen (c s '' (K s ×ˢ Ioo (-eps) eps)))
    (H : ∀ s, K s ≃ₜ
      (hamiltonZeroCircleMap phi ⁻¹' {if s then (beta : C0) else (alpha : C0)} : Set X0))
    (hzero : ∀ s (x : K s), c s (x, 0) = H s x)
    (g : ∀ s, C(K s, C0 × C0)) (hg : ∀ s, IsCoveringMap (g s))
    (hproduct : ∀ s (x : K s) t, t ∈ Icc (-rho) rho →
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        (g s x, (if s then (beta : C0) else (alpha : C0)) +
          (((if s then -1 else 1) * t : ℝ) : C0))) :
    (∃ f : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 f) ∧
      Nonempty (phi.HomotopyRel ⟨f, f.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨f, f.continuous⟩ B0)) ∨
    ∃ side : Bool, HamiltonZeroBoundaryFailureArc e
      (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p
        (if side then beta else alpha) (if side then alpha + p else beta)) phi := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  obtain ⟨r, hr, _, alternatives⟩ := exists_hamiltonZero_first_slab_disk_alternatives
    e d hd phi hphi F ha hab hb he hfront hI hinj K hK hrho c hi hopen H hzero g hg hproduct
  by_cases hfailure : ∃ side : Bool, HamiltonZeroBoundaryFailureArc e
      (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p
        (if side then beta else alpha) (if side then alpha + p else beta)) phi
  · exact Or.inr hfailure
  left
  apply exists_hamiltonZero_rigidity_of_first_slab_endpoints hd phi F ha hab hb he hfront
  intro side
  obtain ⟨collar, cover, hB, _, hc, hci, _, hczero, _, hcover, hcproduct, alternative⟩ :=
    alternatives side
  have data := alternative.resolve_right (fun h => hfailure ⟨side, h⟩)
  have horder : (if side then beta else alpha) < (if side then alpha + p else beta) := by
    cases side <;> dsimp <;> linarith
  have hwidth : (if side then alpha + p else beta) < (if side then beta else alpha) + p := by
    cases side <;> dsimp <;> linarith
  obtain ⟨f, hf, hlocal, hfirst, ⟨G⟩⟩ := data.exists_relative_locally_injective_map
    hd horder hwidth hB hr.le collar hc hci hczero cover hcover
      (fun x => hcproduct x 0 ⟨by linarith, hr.le⟩)
  have hcomp := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap phi) ha hab hb hfront
  have hR : hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p
      (if side then beta else alpha) (if side then alpha + p else beta) =
      (if side then (interior (hamiltonZeroCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p alpha beta))ᶜ
      else hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta) := by
    cases side
    · rfl
    · exact hcomp.symm
  refine ⟨hamiltonZeroHandleMap f, hf.hamiltonZeroHandleMap_of_univ, ?_, ?_, ?_⟩
  · rw [hamiltonZeroAmbientMap_handle, ← hR]
    exact ⟨G⟩
  · intro x hx
    rw [← hamiltonZeroAmbientMap_circle, hamiltonZeroAmbientMap_handle]
    exact hfirst x (hR.symm.subset hx)
  · rw [hamiltonZeroAmbientMap_handle, ← hR]
    exact hlocal

end PoincareConjecture.M76
