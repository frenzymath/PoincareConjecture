import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.CopiedRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PrescribedRimChart









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q2 (Icc (-1 : ℝ) 1)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
  {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (s : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)

theorem exists_stage_replacement_whole_rim_correction
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    (j : Circle ≃ₜ Q2)
    (g : (V2 × ℝ) → s.Carrier) (hg : PolyhedralPLInCharts s.charts g Cyl)
    (gamma : ∀ b, Circle ≃ₜ Annuli.cylinderRimSet b)
    (hgamma : ∀ b, FinitePiecewiseAffineOn
      (fun t : ℝ ↦ (gamma b ((32 * t : ℝ) : Circle) : V2 × ℝ)) (Icc 0 1))
    (hwhole : ∀ b z, g (gamma b z) = s.annulusRim hS b (j z)) :
    ∃ (H : Ann ≃ₜ Cyl) (G : P2 → s.Carrier),
      H.IsFinitePL ∧ PolyhedralPLInCharts s.charts G Ann ∧
      (∀ x : Ann, G x = g (H x)) ∧
      (∀ b z, G (annulusRimPoint b z) = s.annulusRim hS b (j z)) ∧
      (∀ (b : Bool) (x : Ann), depth 8 (x : P2) = (if b then 1 else -1) ↔
        (H x : V2 × ℝ).2 = if b then 1 else -1) ∧
      G '' Ann = g '' Cyl ∧
      ∀ Z : Set s.Carrier,
        (∀ x : Cyl, g x ∈ Z ↔ x.val.2 = -1 ∨ x.val.2 = 1) →
        ∀ x : Ann, G x ∈ Z ↔ depth 8 x = -1 ∨ depth 8 x = 1 := by
  let radial : C(Cyl, Circle) :=
    ⟨fun x ↦ j.symm (chartShellRadial L retained (s.projection (g x))),
      j.symm.continuous.comp ((chartShellRadial L retained).continuous.comp
        (s.projection.continuous.comp hg.continuousOn.domRestrict))⟩
  have hB (b : Bool) : Annuli.cylinderRimSet b ⊆ Cyl := fun _ hx ↦ hx.1
  have hradial (b : Bool) (z : Circle) :
      radial ⟨gamma b z, hB b (gamma b z).property⟩ = z := by
    change j.symm (chartShellRadial L retained (s.projection (g (gamma b z)))) = z
    rw [hwhole, stage_radial_rim L retained s hS hvalues, j.symm_apply_apply]
  obtain ⟨D, hD, hDv⟩ := Annuli.exists_selected_annulus_cylinder
  have hDrim (b : Bool) (x : Ann) :
      depth 8 (x : P2) = (if b then 1 else -1) ↔
        (D x : V2 × ℝ) ∈ Annuli.cylinderRimSet b := by
    constructor
    · intro hx
      exact ⟨(D x).property, (hDv x).trans hx⟩
    · intro hx
      exact (hDv x).symm.trans hx.2
  obtain ⟨H, hH, hHv⟩ := exists_annulus_chart_prescribed_rims D hD
    Annuli.cylinderRimSet hB gamma hgamma hDrim radial hradial
  have hboundary := annulus_chart_boundary_iff_of_prescribed_rims
    H Annuli.cylinderRimSet gamma hHv
  have hlevels (b : Bool) (x : Ann) :
      depth 8 (x : P2) = (if b then 1 else -1) ↔
        (H x : V2 × ℝ).2 = if b then 1 else -1 := by
    exact (hboundary b x).trans
      ⟨fun hx ↦ hx.2, fun hx ↦ ⟨(H x).property, hx⟩⟩
  obtain ⟨p, hp, hpv⟩ := hH
  have hpcopy := hp
  obtain ⟨K, hK, hKs, _⟩ := hpcopy
  have hmap : MapsTo p Ann Cyl := by
    intro x hx
    rw [← hpv ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hGp : PolyhedralPLInCharts s.charts (g ∘ p) Ann := by
    have hh := hg.comp_finitePiecewiseAffineOn K hK (by simpa only [hKs] using hp)
      (fun _ hx ↦ hmap (hKs.subset hx))
    simpa only [hKs] using hh
  have hGv (x : Ann) : (g ∘ p) x = g (H x) := congrArg g (hpv x).symm
  refine ⟨H, g ∘ p, ⟨p, hp, hpv⟩, hGp, hGv, ?_, hlevels, ?_, ?_⟩
  · intro b z
    rw [hGv, hHv]
    exact hwhole b z
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, (hGv ⟨x, hx⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨H.symm ⟨x, hx⟩, (H.symm ⟨x, hx⟩).property, ?_⟩
      rw [hGv, H.apply_symm_apply]
  · intro Z hZ x
    rw [hGv, hZ]
    exact or_congr (hlevels false x).symm (hlevels true x).symm

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
