import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.FiniteMarkedTower
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Approximation.ProtectedCylinder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Coordinates.RetainedShell

set_option autoImplicit false

universe a

open Set Metric Geometry Topology Geometry.OriginalPLTower

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

theorem exists_protected_annulus_tower_with_cutPL
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    {N : Set (V1 × V2)} (hN : IsOpen N)
    (hboundary : frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) :
    ∃ f : (V1 × V2) → U,
      PolyhedralPLInCharts (fun _ : Unit ↦ chart) f source ∧ MapsTo f source R ∧
      (∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x)) ∧
      (∀ x : source, f x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
      ∃ S : SimplicialComplex ℝ (V1 × V2),
        S.faces.Finite ∧ S.space = source ∧
        ∃ (r : U → ℝ) (C : Set U) (s0 t : Stage (fun _ : Unit ↦ chart) S f r C),
          IsCompact C ∧ f '' source ⊆ interior C ∧
          Continuous r ∧
          (∀ i : Unit, LocallyPiecewiseAffineOn
            (r ∘ ((fun _ : Unit ↦ chart) i).symm) ((fun _ : Unit ↦ chart) i).target) ∧
          IsOpenEmbedding s0.projection ∧ Reaches s0 t ∧
          (∀ y ∈ C, (y ∈ R ↔ 0 ≤ r y) ∧
            (y ∈ frontier R ↔ r y = 0) ∧ (y ∈ interior R ↔ 0 < r y)) ∧
          ∀ (Y : Type a) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
            (p : Y → t.Carrier), IsCoveringMap p →
              (∀ x, (p ⁻¹' {x}).ncard = 2) →
              ∀ negative : C(Q2, Y),
                (∀ u : Q2, p (negative u) = t.sourceMap (endpoint false, u)) → False := by
  classical
  obtain ⟨g, hg, hgshell, hgrim, H, _, hH1, _, hHfront⟩ :=
    exists_finitePL_cylinder h hsource hN hboundary hPL
  let u0 : U := Classical.choice (chartShell_nonempty L retained)
  let f : (V1 × V2) → U := fun x ↦
    if hx : g x ∈ (U : Set V3) then ⟨g x, hx⟩ else u0
  have hfu (x : V1 × V2) (hx : x ∈ source) : (f x : V3) = g x := by
    simp only [f, dif_pos (shell_subset_chartShell L retained (hgshell hx))]
  have hfc : ContinuousOn f source := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hgc := hg.continuousOn.comp_continuous continuous_subtype_val (fun x ↦ x.property)
    exact (hgc.subtype_mk (fun x ↦ shell_subset_chartShell L retained (hgshell x.property))).congr
      (fun x ↦ Subtype.ext (hfu x x.property).symm)
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  have hfPL : PolyhedralPLInCharts (fun _ : Unit ↦ chart) f source := by
    rw [← hKs]
    apply polyhedralPLInCharts_of_affine_projections (fun _ : Unit ↦ chart)
      (Subtype.val : U → V3) univ ?_ K hK (hKs.symm ▸ hfc)
      (fun _ _ ↦ mem_univ _) (hKs.symm ▸ hg)
      (fun x hx ↦ hfu x (hKs ▸ hx))
    intro y _
    refine ⟨(), univ, ContinuousAffineMap.id ℝ V3, isOpen_univ, mem_univ y, ?_, ?_⟩
    · intro z _
      exact mem_univ z
    · intro z _
      rfl
  have hfR : MapsTo f source R := by
    intro x hx
    have hmem := (chartDomain_image L retained).symm.subset (hgshell hx)
    obtain ⟨y, hy, hyval⟩ := hmem
    have hxy : f x = y := Subtype.ext ((hfu x hx).trans hyval.symm)
    exact hxy.symm ▸ hy
  have hfFront (x : source) :
      f x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
    rw [chartDomain_frontier_iff L retained hsource (f x)
      ((hfu x x.property).symm ▸ hgshell x.property), hfu x x.property]
    rw [← hH1 x]
    exact hHfront 1 x
  have hdomain := chartDomain_PL L retained he
  let : LocallyCompactSpace U := (chartShell L retained).isOpen.locallyCompactSpace
  obtain ⟨S, hS, hSs, r, W, s, q, C, s0, t, hW, hC, hAC, hCW, hr, hrPL,
    hq, hqPL, hqinj, hF, hs0, hreach, hterm, hcut⟩ :=
    exists_original_annulus_terminal_stage hdomain.compatible hdomain.cover
      hfPL hfR hdomain.halfspace
  refine ⟨f, hfPL, hfR, ?_, hfFront, S, hS, hSs, r, C, s0, t,
    hC, hSs ▸ hAC, hr, hrPL, hs0, hreach, fun y hy ↦ hcut y (hCW hy), hterm⟩
  intro x hx
  exact (hfu x ⟨sphere_subset_closedBall hx.1, hx.2⟩).trans (hgrim x hx)

theorem exists_protected_annulus_tower
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    {N : Set (V1 × V2)} (hN : IsOpen N)
    (hboundary : frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) :
    ∃ f : (V1 × V2) → U,
      PolyhedralPLInCharts (fun _ : Unit ↦ chart) f source ∧ MapsTo f source R ∧
      (∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x)) ∧
      (∀ x : source, f x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
      ∃ S : SimplicialComplex ℝ (V1 × V2),
        S.faces.Finite ∧ S.space = source ∧
        ∃ (r : U → ℝ) (C : Set U) (s0 t : Stage (fun _ : Unit ↦ chart) S f r C),
          IsCompact C ∧ f '' source ⊆ interior C ∧
          Continuous r ∧ IsOpenEmbedding s0.projection ∧ Reaches s0 t ∧
          (∀ y ∈ C, (y ∈ R ↔ 0 ≤ r y) ∧
            (y ∈ frontier R ↔ r y = 0) ∧ (y ∈ interior R ↔ 0 < r y)) ∧
          ∀ (Y : Type a) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
            (p : Y → t.Carrier), IsCoveringMap p →
              (∀ x, (p ⁻¹' {x}).ncard = 2) →
              ∀ negative : C(Q2, Y),
                (∀ u : Q2, p (negative u) = t.sourceMap (endpoint false, u)) → False := by
  obtain ⟨f, hf, hfR, hrim, hfront, S, hS, hSs, r, C, s0, t,
    hC, hfC, hr, _, hs0, hreach, hcut, hterminal⟩ :=
    exists_protected_annulus_tower_with_cutPL.{a} L retained he hsource hN hboundary hPL
  exact ⟨f, hf, hfR, hrim, hfront, S, hS, hSs, r, C, s0, t,
    hC, hfC, hr, hs0, hreach, hcut, hterminal⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
