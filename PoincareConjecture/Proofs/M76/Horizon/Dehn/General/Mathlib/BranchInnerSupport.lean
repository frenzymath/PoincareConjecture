import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchDiskChangeSupport
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotion









set_option autoImplicit false

open Set Metric Topology unitInterval

namespace Geometry

local notation "V3" => (Fin 3 → ℝ)

theorem branch_motion_preserves_inner_carrier
    {X : Type*} [TopologicalSpace X]
    (T : OpenPartialHomeomorph X V3) (J P : Set V3) {ε : ℝ}
    (H : PLCarrierMotion J P ε) (G : I → X ≃ₜ X)
    (hJT : J ⊆ T.target)
    (hformula : ∀ u, EqOn (G u) (T.symm ∘ H.map u ∘ T) T.source) :
    ∀ u, MapsTo (G u) (T.symm '' interior J) (T.symm '' interior J) := by
  intro u x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzT := hJT (interior_subset hz)
  have hm : H.map u z ∈ interior J := by
    have h := ((H.map u).image_interior J).trans (congrArg interior (H.carrier u))
    exact h.subset (mem_image_of_mem (H.map u) hz)
  refine ⟨H.map u z, hm, ?_⟩
  rw [hformula u (T.map_target hzT)]
  change T.symm (H.map u z) = T.symm (H.map u (T (T.symm z)))
  rw [T.right_inv hzT]

theorem branch_disk_change_support_with_endpoint
    {X : Type*} [TopologicalSpace X]
    (T : OpenPartialHomeomorph X V3) (A : Set X) (J K P : Set V3)
    (ρ : ℝ) (hclosed : closedBall (0 : V3) ρ ⊆ interior J)
    (hJT : J ⊆ T.target)
    (hK : K = T '' (A ∩ T.source) ∩ J)
    (hP : P = K \ ball (0 : V3) ρ)
    {ε : ℝ} (H : PLCarrierMotion J P ε) (G : I → X ≃ₜ X)
    (hformula : ∀ u, EqOn (G u) (T.symm ∘ H.map u ∘ T) T.source)
    (hout : ∀ u, EqOn (G u) id (T.symm '' J)ᶜ)
    (hprotected : ∀ u, EqOn (G u) id (T.symm '' P)) :
    let S := T.symm '' closedBall (0 : V3) ρ
    IsCompact S ∧ IsCompact (S ∪ G 1 '' S) ∧
      S ∪ G 1 '' S ⊆ T.symm '' interior J ∧
      ∀ u, EqOn (G u) id (A \ S) := by
  dsimp only
  obtain ⟨hS, hSJ, hfix⟩ := branch_disk_change_support T A J K P ρ
    hclosed hJT hK hP (fun u => G u) hout hprotected
  refine ⟨hS, hS.union (hS.image (G 1).continuous), ?_, hfix⟩
  apply union_subset hSJ
  rintro x ⟨y, hy, rfl⟩
  exact branch_motion_preserves_inner_carrier T J P H G hJT hformula 1 (hSJ hy)

end Geometry
