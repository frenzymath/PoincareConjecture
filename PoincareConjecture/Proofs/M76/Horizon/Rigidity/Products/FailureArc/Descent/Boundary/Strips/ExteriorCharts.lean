import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.Exteriors
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.RetainedCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

private theorem arm_inter_mark_of_parameter {Q : Set P2}
    (c : P2 → P2) {u k : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hk : k ∈ I)
    (hQ : ∀ z ∈ source, c z ∈ Q ↔ z.1 = k) :
    (c '' arm u) ∩ Q = {c (k, u)} := by
  apply Subset.antisymm
  · rintro y ⟨⟨z, hz, rfl⟩, hy⟩
    have hzS : z ∈ source := ⟨hz.1, hz.2.symm ▸ hu⟩
    exact congrArg c (Prod.ext ((hQ z hzS).mp hy) hz.2)
  · rintro y rfl
    exact ⟨⟨(k, u), ⟨hk, rfl⟩, rfl⟩, (hQ (k, u) ⟨hk, hu⟩).mpr rfl⟩

theorem exists_spanning_strip_exterior_square_charts
    {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (c : Bool → P2 → P2)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source)
    (hcin : ∀ i, MapsTo (c i) source (T \ interior S))
    (houter : ∀ i z, z ∈ source → (c i z ∈ frontier T ↔ z.1 = 0))
    (hinner : ∀ i z, z ∈ source → (c i z ∈ frontier S ↔ z.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source)) :
    ∃ (positive : Bool → Bool) (E : Fin 2 → Set P2) (H : ∀ j, Sq ≃ₜ E j),
      let sign := fun (j : Fin 2) (i : Bool) ↦ if j = 0 then positive i else !(positive i)
      (∀ j, (H j).IsFinitePL) ∧
      (∀ j, E j ⊆ T \ interior S) ∧ Disjoint (E 0) (E 1) ∧
      (c false '' source ∪ c true '' source) ∪ (E 0 ∪ E 1) = T \ interior S ∧
      (∀ j i, E j ∩ (c i '' source) = c i '' arm (farArmParameter (sign j i))) ∧
      (∀ j (t : I), (H j ⟨(0, t), by norm_num, t.property⟩ : P2) =
        c false (t, farArmParameter (sign j false))) ∧
      (∀ j (t : I), (H j ⟨(1, t), by norm_num, t.property⟩ : P2) =
        c true (t, farArmParameter (sign j true))) ∧
      (∀ j (z : Sq), (H j z : P2) ∈ frontier T ↔ (z : P2).2 = 0) ∧
      (∀ j (z : Sq), (H j z : P2) ∈ frontier S ↔ (z : P2).2 = 1) := by
  classical
  obtain ⟨positive, E, hE, hES, hEdis, hcover, hcontact, hW⟩ :=
    exists_spanning_strip_exterior_disks hS hT hST c hcPL hci hcin houter hinner hdis
  let sign (j : Fin 2) (i : Bool) := if j = 0 then positive i else !(positive i)
  have hfar (j : Fin 2) (i : Bool) : farArmParameter (sign j i) ∈ Icc (-1 : ℝ) 1 := by
    cases sign j i <;> norm_num [farArmParameter]
  have hQdis : Disjoint (frontier T) (frontier S) := by
    refine disjoint_left.mpr ?_
    intro z hzT hzS
    exact disjoint_left.mp disjoint_interior_frontier (hST (hS.1 hzS)) hzT
  have hex (j : Fin 2) : ∃ H : Sq ≃ₜ E j, H.IsFinitePL ∧
      (∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) =
        c false (t, farArmParameter (sign j false))) ∧
      (∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) =
        c true (t, farArmParameter (sign j true))) ∧
      (∀ z : Sq, (H z : P2) ∈ frontier T ↔ (z : P2).2 = 0) ∧
      (∀ z : Sq, (H z : P2) ∈ frontier S ↔ (z : P2).2 = 1) := by
    obtain ⟨_, _, l, hl, hlval⟩ := exists_embedded_strip_arm_parameter
      (c false) (hcPL false) (hci false) _ (hfar j false)
    obtain ⟨_, _, r, hr, hrval⟩ := exists_embedded_strip_arm_parameter
      (c true) (hcPL true) (hci true) _ (hfar j true)
    obtain ⟨H, hH, hHl, hHr, hHo, hHi⟩ := exists_retained_disk_square_chart
      (hE j) (hW j false) (hW j true)
      (hdis.mono (image_mono (arm_far_subset_source _))
        (image_mono (arm_far_subset_source _)))
      isClosed_frontier isClosed_frontier hQdis
      (arm_inter_mark_of_parameter (c false) (hfar j false) (by norm_num) (houter false))
      (arm_inter_mark_of_parameter (c false) (hfar j false) (by norm_num) (hinner false))
      (arm_inter_mark_of_parameter (c true) (hfar j true) (by norm_num) (houter true))
      (arm_inter_mark_of_parameter (c true) (hfar j true) (by norm_num) (hinner true))
      l r hl hr (hlval _) (hlval _) (hrval _) (hrval _)
    exact ⟨H, hH, fun t ↦ (hHl t).trans (hlval t),
      fun t ↦ (hHr t).trans (hrval t), hHo, hHi⟩
  choose H hH hHl hHr hHo hHi using hex
  exact ⟨positive, E, H, hH, hES, hEdis, hcover, hcontact, hHl, hHr, hHo, hHi⟩

end PoincareConjecture.M76.Dehn
