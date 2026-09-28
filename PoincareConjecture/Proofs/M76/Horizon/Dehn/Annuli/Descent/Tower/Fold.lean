import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.OriginalStep
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.OriginalPLTower

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)



theorem exists_folded_stage_annulus
    (L : Submodule ℤ V2) {α : Type*}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
    {h : OpenPartialHomeomorph (V1 × V2) V3}
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
    {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → chartShell L retained}
    {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
    {s0 st : Stage (fun _ : Unit ↦ (chartShell L retained).openPartialHomeomorphSubtypeCoe
      (chartShell_nonempty L retained)) S f r C}
    (hS : S.space = source) (hSf : S.faces.Finite)
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    (hvalues : ∀ x ∈ Rim, (f x : V3) = h (coordinates x))
    (he : PLDomain (fun _ : Unit ↦ (chartShell L retained).openPartialHomeomorphSubtypeCoe
      (chartShell_nonempty L retained)) (chartDomain L retained))
    (hreach : Reaches s0 st)
    (j : (V1 × V2) → st.Carrier)
    (hj : PolyhedralPLInCharts st.charts j S.space)
    (hji : IsEmbedding (fun x : S.space ↦ j x))
    (hjR : MapsTo j S.space (st.projection ⁻¹' chartDomain L retained))
    (hproper : ∀ x ∈ S.space,
      j x ∈ frontier (st.projection ⁻¹' chartDomain L retained) ↔ x ∈ Rim)
    (hwhole : ∀ (b : Bool) (u : sphere (0 : V2) 1),
      j (endpoint b, u) = st.annulusRim hS b u) :
    ∃ k : (V1 × V2) → s0.Carrier, PolyhedralPLInCharts s0.charts k S.space ∧
      IsEmbedding (fun x : S.space ↦ k x) ∧
      MapsTo k S.space (s0.projection ⁻¹' chartDomain L retained) ∧
      (∀ x ∈ S.space,
        k x ∈ frontier (s0.projection ⁻¹' chartDomain L retained) ↔ x ∈ Rim) ∧
      ∀ (b : Bool) (u : sphere (0 : V2) 1),
        k (endpoint b, u) = s0.annulusRim hS b u := by
  have hinj := prescribed_rim_injective L retained hsource hvalues
  have hdis := prescribed_rim_ranges_disjoint L retained hsource hvalues
  refine backward_fold_reaches (rel := fun a b ↦ Nonempty (Step a b))
    (P := fun s ↦ ∃ k : (V1 × V2) → s.Carrier,
      PolyhedralPLInCharts s.charts k S.space ∧
      IsEmbedding (fun x : S.space ↦ k x) ∧
      MapsTo k S.space (s.projection ⁻¹' chartDomain L retained) ∧
      (∀ x ∈ S.space,
        k x ∈ frontier (s.projection ⁻¹' chartDomain L retained) ↔ x ∈ Rim) ∧
      ∀ (b : Bool) (u : sphere (0 : V2) 1),
        k (endpoint b, u) = s.annulusRim hS b u)
    ?_ hreach ⟨j, hj, hji, hjR, hproper, hwhole⟩
  rintro a b ⟨step⟩ ⟨upper, hu, hui, huR, hup, huw⟩
  exact exists_lower_stage_annulus L retained a b step hS hSf hvalues he
    hu hui huR hup huw hinj hdis

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
