import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Marking
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.CommonDisk



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem local_inclusion_of_shared_exterior
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (m n : E2 → S2) {x : E2} (hx : x ∈ ball 0 1)
    (hml : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x)
    (hnl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ n x)
    (hmark : ∀ z ∈ closedBall (0 : E2) 1, B (m z : E3) = L (n z : E3))
    {X : Set E3} (hp : B (m x : E3) ∈ closure X)
    (hXB : X ⊆ (B '' closedBall (0 : E3) 1)ᶜ)
    (hXL : X ⊆ (L '' closedBall (0 : E3) 1)ᶜ) :
    ∃ V : Set E3, IsOpen V ∧ B (m x : E3) ∈ V ∧
      (L '' closedBall (0 : E3) 1) ∩ V ⊆ B '' closedBall (0 : E3) 1 := by
  obtain ⟨W, hW, hpW, hboundary, _⟩ :=
    Rounding.CommonDisk.exists_boundary_coincidence B L m n hx hml hnl hmark
  obtain ⟨V, hV, hpV, hVW, hconn⟩ :=
    Rounding.CommonDisk.exists_preconnected_exterior_neighborhood B (m x) hW hpW
  have havoid : Disjoint (V ∩ (B '' closedBall (0 : E3) 1)ᶜ)
      (frontier (L '' closedBall (0 : E3) 1)ᶜ) := by
    apply disjoint_left.mpr
    intro y hy hyL
    rw [frontier_compl] at hyL
    change y ∈ frontier (L.toHomeomorph '' closedBall (0 : E3) 1) at hyL
    rw [← L.toHomeomorph.image_frontier, frontier_closedBall (0 : E3) one_ne_zero] at hyL
    have hyB : y ∈ B '' sphere (0 : E3) 1 :=
      (hboundary.symm ▸ (show y ∈ W ∩ (L '' sphere (0 : E3) 1) from
        ⟨hVW hy.1, hyL⟩)).2
    exact hy.2 (image_mono sphere_subset_closedBall hyB)
  obtain ⟨y, hyV, hyX⟩ := mem_closure_iff.mp hp V hV hpV
  have hLclosed : IsClosed (L '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall 0 1).image L.continuous |>.isClosed
  have houtside : V ∩ (B '' closedBall (0 : E3) 1)ᶜ ⊆
      (L '' closedBall (0 : E3) 1)ᶜ :=
    Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
      hLclosed.isOpen_compl hconn havoid ⟨y, ⟨hyV, hXB hyX⟩, hXL hyX⟩
  refine ⟨V, hV, hpV, ?_⟩
  intro y hy
  by_contra hyB
  exact houtside ⟨hy.2, hyB⟩ hy.1



theorem exists_local_inclusion_of_shared_exterior
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {s r : Real} (hr : 0 < r) (hsr : s < r)
    (hB : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hL : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    {X : Set E3} (happroach : g '' closedBall (0 : E2) s ⊆ closure X)
    (hXB : X ⊆ (B '' closedBall (0 : E3) 1)ᶜ)
    (hXL : X ⊆ (L '' closedBall (0 : E3) 1)ᶜ) :
    ∃ V : Set E3, IsOpen V ∧ g '' closedBall (0 : E2) s ⊆ V ∧
      (L '' closedBall (0 : E3) 1) ∩ V ⊆ B '' closedBall (0 : E3) 1 := by
  obtain ⟨p, hp, _⟩ := hB (mem_image_of_mem g (mem_closedBall_self hr.le))
  obtain ⟨m, _, hml, hm, _⟩ :=
    Reverse.exists_ambient_disk_marking_at_radius B g hg hgi hgd hr hB ⟨p, hp⟩
  obtain ⟨n, _, hnl, hn, _⟩ :=
    Reverse.exists_ambient_disk_marking_at_radius L g hg hgi hgd hr hL ⟨p, hp⟩
  let A : Set (Set E3) := {V | IsOpen V ∧
    (L '' closedBall (0 : E3) 1) ∩ V ⊆ B '' closedBall (0 : E3) 1}
  refine ⟨⋃₀ A, isOpen_sUnion (fun V hV => hV.1), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    let x : E2 := r⁻¹ • y
    have hx : x ∈ ball (0 : E2) 1 := by
      rw [mem_ball_zero_iff]
      change ‖r⁻¹ • y‖ < 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      calc
        r⁻¹ * ‖y‖ ≤ r⁻¹ * s :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hy) (inv_pos.mpr hr).le
        _ < r⁻¹ * r := mul_lt_mul_of_pos_left hsr (inv_pos.mpr hr)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    have hmxy : B (m x : E3) = g y := by
      rw [hm x (ball_subset_closedBall hx)]
      simp only [x, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    obtain ⟨V, hV, hxV, hside⟩ := local_inclusion_of_shared_exterior B L m n hx
      (hml x (ball_subset_closedBall hx)) (hnl x (ball_subset_closedBall hx))
      (fun z hz => (hm z hz).trans (hn z hz).symm)
      (hmxy.symm ▸ happroach (mem_image_of_mem g hy)) hXB hXL
    exact mem_sUnion.mpr ⟨V, ⟨hV, hside⟩, hmxy ▸ hxV⟩
  · intro y hy
    obtain ⟨V, hV, hyV⟩ := mem_sUnion.mp hy.2
    exact hV.2 ⟨hy.1, hyV⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps
