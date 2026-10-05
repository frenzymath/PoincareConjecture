import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.Mathlib.QuotientFibersHomeomorph
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.MeridianQuotient
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Isotopy.SolidTorusRelativeHomotopy

/-!
# Topological regluing of both complete meridian faces

An actual source-cut projection with the exact paired-end fibers
descends to a homeomorphism fixing the entire original boundary.
Both relative homotopies retain literal original-handle values.
This proves no existence of source cut data and asserts no PL
descent. See rigidity derivation 005.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

/-- The actual compact-cut projection and its complete paired
end fibers produce a homeomorphism with exactly the prescribed
cut values and the whole original boundary fixed.
See rigidity derivation 005. -/
theorem exists_hamiltonSolidTorus_regluing
    (r : C(HamiltonMeridianClosedCut, H)) (hr : Function.Surjective r)
    (hfib : ∀ a b : HamiltonMeridianClosedCut,
      r a = r b ↔ a.1 = b.1 ∧ ((a.2 : ℝ) = b.2 ∨
        ((a.2 : ℝ) = 0 ∧ (b.2 : ℝ) = p) ∨
        ((a.2 : ℝ) = p ∧ (b.2 : ℝ) = 0)))
    (hboundary : ∀ a : HamiltonMeridianClosedCut, ‖(a.1 : V2)‖ = 1 →
      r a = hamiltonMeridianQuotient a) :
    ∃ g : H ≃ₜ H,
      (∀ a : HamiltonMeridianClosedCut, g (hamiltonMeridianQuotient a) = r a) ∧
      ∀ x ∈ B, g x = x := by
  let : T2Space H := ((Homeomorph.refl (closedBall (0 : V2) 1)).prodCongr
    hamiltonSolidTorusCircleEquiv).isEmbedding.t2Space
  have hqr : Topology.IsQuotientMap r :=
    r.continuous.isClosedMap.isQuotientMap r.continuous hr
  obtain ⟨g, hg⟩ := isQuotientMap_hamiltonMeridianQuotient.exists_homeomorph_of_fibers
    hqr (fun a b => (hamiltonMeridianQuotient_eq_iff a b).trans (hfib a b).symm)
  refine ⟨g, hg, ?_⟩
  intro x hx
  obtain ⟨a, rfl⟩ := hamiltonMeridianQuotient_surjective x
  exact (hg a).trans (hboundary a ((hamiltonMeridianQuotient_mem_boundary a).mp hx))

/-- The same reglued homeomorphism has both literal relative
homotopies required by the original marked solid torus. Source
cut existence and chartwise PL descent remain separate obligations.
See rigidity derivations 003 and 005. -/
theorem exists_hamiltonSolidTorus_regluing_with_homotopies
    (r : C(HamiltonMeridianClosedCut, H)) (hr : Function.Surjective r)
    (hfib : ∀ a b : HamiltonMeridianClosedCut,
      r a = r b ↔ a.1 = b.1 ∧ ((a.2 : ℝ) = b.2 ∨
        ((a.2 : ℝ) = 0 ∧ (b.2 : ℝ) = p) ∨
        ((a.2 : ℝ) = p ∧ (b.2 : ℝ) = 0)))
    (hboundary : ∀ a : HamiltonMeridianClosedCut, ‖(a.1 : V2)‖ = 1 →
      r a = hamiltonMeridianQuotient a)
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ g : H ≃ₜ H,
      (∀ a : HamiltonMeridianClosedCut, g (hamiltonMeridianQuotient a) = r a) ∧
      (∀ x ∈ B, g x = x) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel ⟨g, g.continuous⟩ B) := by
  obtain ⟨g, hg, hgB⟩ := exists_hamiltonSolidTorus_regluing r hr hfib hboundary
  exact ⟨g, hg, hgB,
    exists_hamiltonSolidTorus_two_relative_homotopies phi ⟨g, g.continuous⟩ F hgB⟩

end PoincareMT.M76
