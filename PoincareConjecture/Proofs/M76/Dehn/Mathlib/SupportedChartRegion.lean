import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasCorrection

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

theorem supported_chart_preimage_region {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X]
    (Q : OpenPartialHomeomorph E X) (H : E ≃ₜ E) (F : X ≃ₜ X)
    {K B : Set E} {R : Set X} (hKQ : K ⊆ Q.source)
    (hfix : EqOn H id Kᶜ)
    (hFQ : EqOn F (Q.symm.trans (H.toOpenPartialHomeomorph.trans Q)) Q.target)
    (hFout : EqOn F id (Q '' K)ᶜ)
    (hmodel : ∀ z ∈ Q.source, Q z ∈ R ↔ z ∈ B)
    (hB : ∀ z, H z ∈ B ↔ z ∈ B) : F ⁻¹' R = R := by
  have hsource : MapsTo H Q.source Q.source := by
    intro x hx
    by_contra hn
    have hnotK : H x ∉ K := fun h => hn (hKQ h)
    have he : H x = x := H.injective (hfix hnotK)
    exact hn (he.symm ▸ hx)
  ext y
  change F y ∈ R ↔ y ∈ R
  by_cases hy : y ∈ Q.target
  · rw [hFQ hy]
    change Q (H (Q.symm y)) ∈ R ↔ y ∈ R
    rw [hmodel _ (hsource (Q.map_target hy)), hB]
    simpa only [Q.right_inv hy] using (hmodel _ (Q.map_target hy)).symm
  · have hout : y ∉ Q '' K := by
      rintro ⟨z, hz, rfl⟩
      exact hy (Q.map_source (hKQ hz))
    rw [hFout hout]
    rfl

end OpenPartialHomeomorph

namespace Homeomorph

theorem preimage_frontier_mark_of_supported {X : Type*} [TopologicalSpace X]
    (F : X ≃ₜ X) {R C W : Set X} (hR : F ⁻¹' R = R)
    (hfix : EqOn F id Cᶜ) (hCW : C ⊆ W) :
    F ⁻¹' frontier R = frontier R ∧
      F ⁻¹' (frontier R ∩ W) = frontier R ∩ W := by
  have hfront : F ⁻¹' frontier R = frontier R := by
    rw [F.preimage_frontier, hR]
  have hW : F ⁻¹' W = W := F.injective.preimage_eq_self_of_eqOn_compl
    (fun _ hx => hfix (fun h => hx (hCW h)))
  exact ⟨hfront, by rw [preimage_inter, hfront, hW]⟩

end Homeomorph

namespace Topology

theorem exists_open_frontier_mark {X : Type*} [TopologicalSpace X]
    {R F : Set X} (hF : F ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F)) :
    ∃ W : Set X, IsOpen W ∧ F = frontier R ∩ W := by
  obtain ⟨W, hW, heq⟩ := isOpen_induced_iff.mp hopen
  refine ⟨W, hW, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨hF hx, ?_⟩
    have hm : (⟨x, hF hx⟩ : frontier R) ∈ (Subtype.val : frontier R → X) ⁻¹' F := hx
    rw [← heq] at hm
    exact hm
  · rintro ⟨hxR, hxW⟩
    have hm : (⟨x, hxR⟩ : frontier R) ∈ (Subtype.val : frontier R → X) ⁻¹' W := hxW
    rw [heq] at hm
    exact hm

end Topology
