import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.FiniteMarkedTower









set_option autoImplicit false

universe w z

open Set Metric Topology Geometry
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1




theorem exists_original_singular_annulus_terminal_region
    {M : Type w} {ι : Type z} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {R : Set M} (he : PLDomain e R)
    {f : (V1 × V2) → M}
    (hf : PolyhedralPLInCharts e f ProtectedAnnulus.source)
    (hfR : MapsTo f ProtectedAnnulus.source R)
    (hfront : ∀ u : Q2, f (ProtectedAnnulus.endpoint false, u) ∈ frontier R) :
    ∃ S : SimplicialComplex ℝ (V1 × V2),
      S.faces.Finite ∧ S.space = ProtectedAnnulus.source ∧
      ∃ (r : M → ℝ) (C : Set M) (s0 t : Stage e S f r C),
        IsOpenEmbedding s0.projection ∧ Reaches s0 t ∧
        Nonempty (MarkedTerminalRegion t R) ∧
        ∀ (Y : Type w) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
          (p : Y → t.Carrier), IsCoveringMap p →
          (∀ x, (p ⁻¹' {x}).ncard = 2) →
          ∀ negative : C(Q2, Y),
            (∀ u, p (negative u) = t.sourceMap (ProtectedAnnulus.endpoint false, u)) → False := by
  obtain ⟨S, hS, hsource, r, W, s, q, C, s0, t, _, _, _, hCW, hr, hrPL,
    _, _, _, _, hs0, hreach, hterm, hcut⟩ :=
    exists_original_annulus_terminal_stage he.compatible he.cover hf hfR he.halfspace
  have hregion := t.nonempty_terminal_region_of_marked_loop hS hsource
    (hsource.symm ▸ hfR) he.closed hr hrPL
    (fun x hx => (hcut x (hCW hx)).1)
    (fun x hx => (hcut x (hCW hx)).2.1) he.halfspace hfront hterm
  exact ⟨S, hS, hsource, r, C, s0, t, hs0, hreach, hregion, hterm⟩

end Geometry.OriginalPLTower
