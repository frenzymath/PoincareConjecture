import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.Termination
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Planar.OriginalProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.OriginalParameters
import PoincareConjecture.Proofs.M76.Dehn.OriginalRegionBranchCharts

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "Q" => sphere (0 : V2) 1
local notation "Rim" => Set.prod (sphere (0 : V1) 1) Q

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph A V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
  {S : SimplicialComplex ℝ A} {f : A → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (s t : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)

theorem exists_lower_stage_annulus (step : Geometry.OriginalPLTower.Step s t)
    (hS : S.space = source) (hSf : S.faces.Finite)
    (hvalues : ∀ x ∈ Rim, (f x : V3) = h (coordinates x))
    {R : Set (chartShell L retained)}
    (he : PLDomain (fun _ : Unit ↦
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
        (chartShell L retained) (chartShell_nonempty L retained)) R)
    {j : A → t.Carrier} (hj : PolyhedralPLInCharts t.charts j S.space)
    (hji : IsEmbedding (fun x : S.space ↦ j x))
    (hjR : MapsTo j S.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ S.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Rim)
    (hwhole : ∀ (b : Bool) (u : Q), j (endpoint b, u) = t.annulusRim hS b u)
    (hinj : ∀ b : Bool, Function.Injective (fun u : Q ↦ f (endpoint b, u)))
    (hdis : Disjoint (range (fun u : Q ↦ f (endpoint false, u)))
      (range (fun u : Q ↦ f (endpoint true, u)))) :
    ∃ g : A → s.Carrier, PolyhedralPLInCharts s.charts g S.space ∧
      IsEmbedding (fun x : S.space ↦ g x) ∧ MapsTo g S.space (s.projection ⁻¹' R) ∧
      (∀ x ∈ S.space, g x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim) ∧
      ∀ (b : Bool) (u : Q), g (endpoint b, u) = s.annulusRim hS b u := by
  obtain ⟨period, H, _, p, _, _, hHi, hHv, hHb, _, _, _, _, hp, hpR, hpfront,
    hpwhole, _, _, _, hpinterior, hpraw, _, ⟨M⟩, _⟩ :=
    step.exists_ordinary_planar_annulus_circle_components he hS hSf hj hji hjR hproper
      hwhole hinj hdis
  obtain ⟨g, hg, hgi, hgR, hgfront, hgwhole⟩ :=
    exists_embedded_planar_stage_annulus L retained s hS hvalues period
      (s.plDomain_region he) p hp hpR hpfront hpwhole M hpinterior hpraw
  exact s.exists_original_parameter_annulus hS period H hHi hHv hHb
    g hg hgi hgR hgfront hgwhole

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
