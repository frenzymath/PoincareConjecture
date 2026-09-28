import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.NestedCylinder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.CopiedRims



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_copied_original_rims
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {l r : ℝ} {A : Fin 2 → Set P2}
    {B : ∀ k, OrientedPolygonCollar l r (A k)} {j : Fin 2}
    {f : P2 → X} {τ : (P2 × ℝ) → X}
    (D : NestedResolvingCylinder (L := 8) (d := 1) e B j f τ)
    (hA : ∀ k, A k ⊆ {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1})
    (henclosing : annulusSquare 8 1 ⊆ (B j.rev).outer.inside) :
    ∃ gamma : ∀ b, Circle ≃ₜ cylinderRimSet b,
      (∀ b, FinitePiecewiseAffineOn
        (fun t : ℝ ↦ (gamma b ((32 * t : ℝ) : Circle) : V2 × ℝ)) (Icc 0 1)) ∧
      (∀ b z, D.map (gamma b z) = f (annulusRimPoint b z)) ∧
      (∀ z, ∃ hz, (gamma false z : V2 × ℝ) =
        D.copyO ⟨annulusRimPoint false z, hz⟩) ∧
      ∀ z, ∃ hz, (gamma true z : V2 × ℝ) =
        D.copyI ⟨annulusRimPoint true z, hz⟩ := by
  have hrimO (z : Circle) : (annulusRimPoint false z : P2) ∈
      annulusSquare 8 (-1) \ (B j).outer.inside := by
    have hz : depth 8 (annulusRimPoint false z : P2) = -1 := depth_annulusRimPoint false z
    refine ⟨(mem_annulusSquare_iff 8 (-1) _).mpr hz.ge, ?_⟩
    intro hh
    have h := (oriented_collar_disk_or_enclosing (B j) (hA j)).2.2.1 (subset_closure hh)
    have hlt := (mem_interior_annulusSquare_iff 8 (-1) _).mp h
    linarith
  have hrimI (z : Circle) : (annulusRimPoint true z : P2) ∈
      closure (B j.rev).inner.inside \ interior (annulusSquare 8 1) := by
    have hz : depth 8 (annulusRimPoint true z : P2) = 1 := depth_annulusRimPoint true z
    refine ⟨subset_closure (((oriented_collar_enclosing_iff (B j.rev) (hA j.rev)).mp
      henclosing) ((mem_annulusSquare_iff 8 1 _).mpr hz.ge)), ?_⟩
    intro hh
    have hlt := (mem_interior_annulusSquare_iff 8 1 _).mp hh
    linarith
  have hlevelO (x) : (D.copyO x).val.2 = -1 ↔ depth 8 x = -1 := by
    rw [D.copyO_level]
    have h := D.outer_end (D.outer.symm x)
    rw [D.outer.apply_symm_apply] at h
    exact (show ((D.outer.symm x).val.2 - 3) / 4 = -1 ↔
      (D.outer.symm x).val.2 = -1 by constructor <;> intro hh <;> linarith).trans h
  have hlevelI (x) : (D.copyI x).val.2 = 1 ↔ depth 8 x = 1 := by
    rw [D.copyI_level]
    have h := D.inner_end (D.inner.symm x)
    rw [D.inner.apply_symm_apply] at h
    exact (show ((D.inner.symm x).val.2 + 1) / 2 = 1 ↔
      (D.inner.symm x).val.2 = 1 by constructor <;> intro hh <;> linarith).trans h
  obtain ⟨gammaO, hgammaO, hgammaOPL⟩ := exists_copied_rim_chart false
    D.copyO D.copyO_PL D.outer_source hrimO
    (fun x hx ↦ ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩)
    (fun x hx ↦ ⟨hx.1.1, hx.1.2.1, by
      have hh : x.2 = -1 := hx.2
      change x.2 ≤ -(1 / 2 : ℝ)
      linarith⟩)
    hlevelO
  obtain ⟨gammaI, hgammaI, hgammaIPL⟩ := exists_copied_rim_chart true
    D.copyI D.copyI_PL D.inner_source hrimI
    (fun x hx ↦ ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩)
    (fun x hx ↦ ⟨hx.1.1, by
      have hh : x.2 = 1 := hx.2
      change (0 : ℝ) ≤ x.2
      linarith, hx.1.2.2⟩)
    hlevelI
  let gamma : ∀ b, Circle ≃ₜ cylinderRimSet b := fun b ↦
    match b with
    | false => gammaO
    | true => gammaI
  refine ⟨gamma, ?_, ?_, fun z ↦ ⟨hrimO z, hgammaO z⟩,
    fun z ↦ ⟨hrimI z, hgammaI z⟩⟩
  · intro b
    cases b
    · exact hgammaOPL
    · exact hgammaIPL
  · intro b z
    cases b
    · change D.map (gammaO z) = _
      rw [hgammaO]
      exact D.keepO _
    · change D.map (gammaI z) = _
      rw [hgammaI]
      exact D.keepI _

end PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder
