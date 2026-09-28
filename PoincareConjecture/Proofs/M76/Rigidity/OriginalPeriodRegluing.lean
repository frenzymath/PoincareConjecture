import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodPL
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodImage
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodFibers
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodLateral
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCutProjection
import PoincareConjecture.Proofs.M76.Rigidity.SolidTorusPLRegluing

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H0" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B0" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

theorem exists_period_PL_regluing {α β : Type*}
    {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3} {j : V2 → X}
    (P : OriginalDiskProduct e R j)
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) (he : PLDomain e R)
    {a : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
    (u : E → X) (hu : PolyhedralPLInCharts e u (D ×ˢ Icc (a / 2) (p - a / 2)))
    (hvalue : ∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X))
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2)))
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (hlateral : ∀ z ∈ Q, ∀ t ∈ Icc (a / 2) (p - a / 2),
      u (z, t) = hamiltonMeridianCutAmbientMap (z, t))
    (hcover : P.closedStrip ∪ P.cutCarrier = R)
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ g : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 2) (Fin 1) L g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨g, g.continuous⟩ B0) := by
  have hPL := P.polyhedral_periodCutMap he ha hgap u hu hlower hupper
  have himage := P.image_periodCutMap ha hgap H u hvalue hlower hupper hcover
  obtain ⟨r, hr, hfib, hboundary, hrvalue⟩ :=
    exists_hamiltonMeridianCutProjection (P.periodCutMap a p u) hPL.continuousOn himage
      (fun z hz w hw => P.periodCutMap_eq_iff ha hgap H u hvalue hlower hupper hz hw)
      (by
        intro z hz
        exact P.periodCutMap_lateral ha hgap u hlower hupper hmark hlateral hz)
  exact exists_hamiltonSolidTorus_PL_regluing hd he r hr hfib hboundary
    (P.periodCutMap a p u) hPL hrvalue phi F

end PoincareConjecture.M76.OriginalDiskProduct
