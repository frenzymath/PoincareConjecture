import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.CompactRegion

set_option autoImplicit false

open Set Metric Topology Geometry Geometry.OriginalPLTower

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)

local notation "U" => chartShell L retained
local notation "R" => chartDomain L retained
local notation "chart" => TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
  (chartShell L retained) (chartShell_nonempty L retained)

structure ProtectedAnnulusTerminalData where
  map : (V1 × V2) → U
  map_PL : PolyhedralPLInCharts (fun _ : Unit => chart) map source
  map_region : MapsTo map source R
  boundary_values : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (map x : V3) = h (coordinates x)
  frontier_iff : ∀ x : source, map x ∈ frontier R ↔
    (x : V1 × V2).1 ∈ sphere (0 : V1) 1
  source_complex : SimplicialComplex ℝ (V1 × V2)
  source_finite : source_complex.faces.Finite
  source_space : source_complex.space = source
  cut : U → ℝ
  cut_continuous : Continuous cut
  cut_PL : ∀ i : Unit, LocallyPiecewiseAffineOn
    (cut ∘ ((fun _ : Unit => chart) i).symm) ((fun _ : Unit => chart) i).target
  core : Set U
  core_compact : IsCompact core
  core_contains : map '' source ⊆ interior core
  cut_values : ∀ y ∈ core, (y ∈ R ↔ 0 ≤ cut y) ∧
    (y ∈ frontier R ↔ cut y = 0) ∧ (y ∈ interior R ↔ 0 < cut y)
  initial : Stage (fun _ : Unit => chart) source_complex map cut core
  stage : Stage (fun _ : Unit => chart) source_complex map cut core
  initial_open : IsOpenEmbedding initial.projection
  reaches : Reaches initial stage
  terminal : ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    (p : Y → stage.Carrier), IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
    ∀ negative : C(Q2, Y),
      (∀ u, p (negative u) = stage.sourceMap (endpoint false, u)) → False
  compact_region : MarkedTerminalRegion stage R

theorem nonempty_protected_annulus_terminal_region
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    {N : Set (V1 × V2)} (hN : IsOpen N)
    (hboundary : frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) :
    Nonempty (ProtectedAnnulusTerminalData L retained) := by
  classical
  obtain ⟨f, hf, hfR, hvalues, hfront, S, hS, hSs, r, C, s0, st,
    hC, hAC, hr, hrPL, hs0, hreach, hcut, hterminal⟩ :=
    exists_protected_annulus_tower_with_cutPL L retained he hsource hN hboundary hPL
  have hdomain := chartDomain_PL L retained he
  have hfrontRim (u : Q2) : f (endpoint false, u) ∈ frontier R :=
    (hfront ⟨(endpoint false, u),
      ⟨sphere_subset_closedBall (endpoint_mem_sphere false), u.property⟩⟩).mpr
      (endpoint_mem_sphere false)
  obtain ⟨region⟩ := st.nonempty_marked_terminal_region hS hSs
    (hSs.symm ▸ hfR) hdomain.closed hr hrPL
    (fun x hx => (hcut x hx).1) (fun x hx => (hcut x hx).2.1)
    hdomain.halfspace (prescribed_rim_injective L retained hsource hvalues false)
    hfrontRim hterminal
  exact ⟨{
    map := f
    map_PL := hf
    map_region := hfR
    boundary_values := hvalues
    frontier_iff := hfront
    source_complex := S
    source_finite := hS
    source_space := hSs
    cut := r
    cut_continuous := hr
    cut_PL := hrPL
    core := C
    core_compact := hC
    core_contains := hAC
    cut_values := hcut
    initial := s0
    stage := st
    initial_open := hs0
    reaches := hreach
    terminal := hterminal
    compact_region := region }⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
