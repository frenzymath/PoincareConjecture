import PoincareConjecture.Proofs.M76.Rigidity.SolidTorusRegluing
import PoincareConjecture.Proofs.M76.Rigidity.MeridianPLDescent
import PoincareConjecture.Proofs.M76.Rigidity.HomeomorphInverseCoordinates










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))





theorem exists_hamiltonSolidTorus_PL_regluing
    {α β : Type*}
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (he : PLDomain e R)
    (r : C(HamiltonMeridianClosedCut, H)) (hr : Function.Surjective r)
    (hfib : ∀ a b : HamiltonMeridianClosedCut,
      r a = r b ↔ a.1 = b.1 ∧ ((a.2 : ℝ) = b.2 ∨
        ((a.2 : ℝ) = 0 ∧ (b.2 : ℝ) = p) ∨
        ((a.2 : ℝ) = p ∧ (b.2 : ℝ) = 0)))
    (hboundary : ∀ a : HamiltonMeridianClosedCut, ‖(a.1 : V2)‖ = 1 →
      r a = hamiltonMeridianQuotient a)
    (u : E → X) (hu : PolyhedralPLInCharts e u (D ×ˢ Icc 0 p))
    (huvalue : ∀ a : HamiltonMeridianClosedCut,
      u ((a.1 : V2), (a.2 : ℝ)) =
        ((latticeHandleDomainEquiv (Fin 2) (Fin 1) L).symm (r a) : X))
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ g : H ≃ₜ H,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 2) (Fin 1) L g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel ⟨g, g.continuous⟩ B) := by
  obtain ⟨h, hh, hhB⟩ := exists_hamiltonSolidTorus_regluing r hr hfib hboundary
  let Q := latticeHandleDomainEquiv (Fin 2) (Fin 1) L
  let hR := latticeHandleHomeomorphInDomain (Fin 2) (Fin 1) L h
  have hcomposite : PolyhedralPLInCharts e
      (fun z => (hR (hamiltonMeridianParameter z) : X)) (D ×ˢ Icc 0 p) :=
    hu.congr (by
      intro z hz
      let a : HamiltonMeridianClosedCut := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
      have hq : Q (hamiltonMeridianParameter z) = hamiltonMeridianQuotient a :=
        hamiltonMeridianParameter_domainEquiv a.1 a.2
      have hvalue : hR (hamiltonMeridianParameter z) = Q.symm (r a) := by
        change Q.symm (h (Q (hamiltonMeridianParameter z))) = Q.symm (r a)
        rw [hq, hh a]
      exact (huvalue a).trans (congrArg Subtype.val hvalue).symm)
  have hPL : ChartwisePLMap d e ⟨hR, hR.continuous⟩ :=
    hd.chartwisePLMap_of_meridianCut he ⟨hR, hR.continuous⟩ hcomposite
  have hPLinv : ChartwisePLHomeomorph e d
      (latticeHandleHomeomorphInDomain (Fin 2) (Fin 1) L h.symm) := by
    change ChartwisePLHomeomorph e d hR.symm
    exact hPL.inverse_homeomorph.chartwisePLHomeomorph
  have hB (x : H) (hx : x ∈ B) : h.symm x = x := by
    have hval := congrArg h.symm (hhB x hx)
    rw [h.symm_apply_apply] at hval
    exact hval.symm
  obtain ⟨hphi, hid⟩ := exists_hamiltonSolidTorus_two_relative_homotopies
    phi ⟨h.symm, h.symm.continuous⟩ F hB
  exact ⟨h.symm, hPLinv, hphi, hid⟩

end PoincareConjecture.M76
