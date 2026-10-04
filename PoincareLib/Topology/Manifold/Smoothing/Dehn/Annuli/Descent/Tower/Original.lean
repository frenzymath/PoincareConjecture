import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Descent.Tower.Terminal
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Descent.Tower.Fold
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Descent.Tower.Projection

/-!
# The embedded protected chart annulus from the original handle

The retained original handle constructs the marked tower and its terminal
annulus. Actual finite circle surgeries fold that annulus through each covering
step, and the initial open embedding restores both complete original rim maps.
See Hamilton 1976, p. 67, and Shapiro--Whitehead 1958, section 4.
-/

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.OriginalPLTower

namespace PoincareMT.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

/-- Original protected handle data construct the embedded proper annulus with
both prescribed full boundary maps. No tower, surgery or annulus is supplied. -/
theorem exists_embedded_chart_annulus
    (L : Submodule ℤ V2) {α : Type*}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
    {h : OpenPartialHomeomorph (V1 × V2) V3}
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    {N : Set (V1 × V2)} (hN : IsOpen N)
    (hboundary : frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) :
    ∃ k : (V1 × V2) → chartShell L retained,
      PolyhedralPLInCharts (fun _ : Unit ↦ (chartShell L retained).openPartialHomeomorphSubtypeCoe
        (chartShell_nonempty L retained)) k source ∧
      IsEmbedding (fun x : source ↦ k x) ∧ MapsTo k source (chartDomain L retained) ∧
      (∀ x ∈ Rim, (k x : V3) = h (coordinates x)) ∧
      ∀ x : source, k x ∈ frontier (chartDomain L retained) ↔
        x.val.1 ∈ sphere (0 : V1) 1 := by
  obtain ⟨d⟩ := nonempty_protected_annulus_terminal_region L retained he hsource hN hboundary hPL
  obtain ⟨j, hj, hji, hjR, hjfront, hjwhole⟩ :=
    d.exists_embedded_terminal_annulus L retained hsource
  obtain ⟨k, hk, hki, hkR, hkfront, hkwhole⟩ :=
    exists_folded_stage_annulus L retained d.source_space d.source_finite hsource
      d.boundary_values (chartDomain_PL L retained he) d.reaches
      j hj hji hjR hjfront hjwhole
  exact d.exists_chart_annulus_of_initial L retained k hk hki hkR hkfront hkwhole

end PoincareMT.M76.Dehn.ProtectedAnnulus
