import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Marking
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.CommonDisk

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_open_boundary_patch_for_disk
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 -> E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {s r : Real} (hr : 0 < r) (hsr : s < r)
    (hsub : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1) :
    ∃ U : Set E3, IsOpen U ∧ g '' closedBall (0 : E2) s ⊆ U ∧
      U ∩ (B '' sphere (0 : E3) 1) ⊆ g '' closedBall (0 : E2) r := by
  obtain ⟨p, hp, _⟩ := hsub (mem_image_of_mem g (mem_closedBall_self hr.le))
  obtain ⟨m, _, hml, hm, hmrange⟩ :=
    exists_ambient_disk_marking_at_radius B g hg hgi hgd hr hsub ⟨p, hp⟩
  let A : Set (Set E3) := {W | IsOpen W ∧
    W ∩ (B '' sphere (0 : E3) 1) ⊆ g '' closedBall (0 : E2) r}
  refine ⟨⋃₀ A, isOpen_sUnion (fun W hW => hW.1), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    let z : E2 := r⁻¹ • y
    have hz : z ∈ ball (0 : E2) 1 := by
      rw [mem_ball_zero_iff]
      change ‖r⁻¹ • y‖ < 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      calc
        r⁻¹ * ‖y‖ ≤ r⁻¹ * s :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hy) (inv_pos.mpr hr).le
        _ < r⁻¹ * r := mul_lt_mul_of_pos_left hsr (inv_pos.mpr hr)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    obtain ⟨W, hW, hzW, hWsub⟩ :=
      Rounding.CommonDisk.exists_boundary_patch B m hz (hml z (ball_subset_closedBall hz))
    have hmyz : B (m z : E3) = g y := by
      rw [hm z (ball_subset_closedBall hz)]
      simp only [z, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    refine mem_sUnion.mpr ⟨W, ⟨hW, ?_⟩, hmyz ▸ hzW⟩
    exact hWsub.trans ((image_mono ball_subset_closedBall).trans_eq hmrange)
  · rintro y ⟨hy, hyS⟩
    obtain ⟨W, hW, hyW⟩ := mem_sUnion.mp hy
    exact hW.2 ⟨hyW, hyS⟩

end Poincare.Manifold.Schoenflies.Reverse
