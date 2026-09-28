import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.ShellSquareCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

namespace NestedShellSquareCharts

variable {S T : Set P2} {D : NestedShellDissection S T} (C : NestedShellSquareCharts D)

theorem agree_at_side (z : Sq) (hz : (z : P2).1 = 0 ∨ (z : P2).1 = 1) :
    (C.chart 0 z : P2) = C.chart 1 z := by
  rcases hz with hz | hz
  · have he : z = ⟨(0, z.val.2), by norm_num, z.property.2⟩ :=
      Subtype.ext (Prod.ext hz rfl)
    rw [he]
    exact C.left_agree ⟨z.val.2, z.property.2⟩
  · have he : z = ⟨(1, z.val.2), by norm_num, z.property.2⟩ :=
      Subtype.ext (Prod.ext hz rfl)
    rw [he]
    exact C.right_agree ⟨z.val.2, z.property.2⟩

theorem mem_other_disk_iff (z : Sq) :
    (C.chart 0 z : P2) ∈ D.disk 1 ↔ (z : P2).1 = 0 ∨ (z : P2).1 = 1 := by
  constructor
  · intro hz
    have hh := D.disk_inter.subset ⟨(C.chart 0 z).property, hz⟩
    exact hh.elim (fun h ↦ Or.inl ((C.left_iff 0 z).mp h))
      (fun h ↦ Or.inr ((C.right_iff 0 z).mp h))
  · intro hz
    exact hz.elim (fun h ↦ D.left_subset_disk 1 ((C.left_iff 0 z).mpr h))
      (fun h ↦ D.right_subset_disk 1 ((C.right_iff 0 z).mpr h))

theorem inverse_agree {z : P2} (hz₀ : z ∈ D.disk 0) (hz₁ : z ∈ D.disk 1) :
    (C.chart 0).symm ⟨z, hz₀⟩ = (C.chart 1).symm ⟨z, hz₁⟩ := by
  let u := (C.chart 0).symm ⟨z, hz₀⟩
  have hu : (u : P2).1 = 0 ∨ (u : P2).1 = 1 := by
    apply (C.mem_other_disk_iff u).mp
    simpa only [u, Homeomorph.apply_symm_apply] using hz₁
  apply (C.chart 1).injective
  apply Subtype.ext
  rw [Homeomorph.apply_symm_apply]
  exact (C.agree_at_side u hu).symm.trans
    (congrArg Subtype.val ((C.chart 0).apply_symm_apply ⟨z, hz₀⟩))

end NestedShellSquareCharts



theorem exists_nested_shell_homeomorph {S T S' T' : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (hS' : IsFinitePLBallPair P2 S' (frontier S'))
    (hT' : IsFinitePLBallPair P2 T' (frontier T')) (hST' : S' ⊆ interior T') :
    ∃ H : (T \ interior S : Set P2) ≃ₜ (T' \ interior S' : Set P2), H.IsFinitePL ∧
      (∀ z : (T \ interior S : Set P2), (z : P2) ∈ frontier T ↔ (H z : P2) ∈ frontier T') ∧
      (∀ z : (T \ interior S : Set P2), (z : P2) ∈ frontier S ↔ (H z : P2) ∈ frontier S') := by
  obtain ⟨D⟩ := exists_nested_shell_dissection hS hT hST
  obtain ⟨E⟩ := exists_nested_shell_dissection hS' hT' hST'
  obtain ⟨C⟩ := D.nonempty_square_charts
  obtain ⟨F⟩ := E.nonempty_square_charts
  let e (j : Fin 2) : D.disk j ≃ₜ E.disk j := (C.chart j).symm.trans (F.chart j)
  have he (j : Fin 2) : (e j).IsFinitePL := (C.finitePL j).symm.trans (F.finitePL j)
  have hcross (z : D.disk 0) : (z : P2) ∈ D.disk 1 ↔ (e 0 z : P2) ∈ E.disk 1 := by
    have hh := (C.mem_other_disk_iff ((C.chart 0).symm z)).trans
      (F.mem_other_disk_iff ((C.chart 0).symm z)).symm
    simpa only [e, Homeomorph.trans_apply, Homeomorph.apply_symm_apply] using hh
  have hagree (z : P2) (hz₀ : z ∈ D.disk 0) (hz₁ : z ∈ D.disk 1) :
      (e 0 ⟨z, hz₀⟩ : P2) = e 1 ⟨z, hz₁⟩ := by
    change (F.chart 0 ((C.chart 0).symm ⟨z, hz₀⟩) : P2) =
      F.chart 1 ((C.chart 1).symm ⟨z, hz₁⟩)
    have hh : ((C.chart 0).symm ⟨z, hz₀⟩ : P2).1 = 0 ∨
        ((C.chart 0).symm ⟨z, hz₀⟩ : P2).1 = 1 := by
      apply (C.mem_other_disk_iff _).mp
      simpa only [Homeomorph.apply_symm_apply] using hz₁
    exact (F.agree_at_side _ hh).trans
      (congrArg (fun w : Sq ↦ (F.chart 1 w : P2)) (C.inverse_agree hz₀ hz₁))
  have houter (j : Fin 2) (z : D.disk j) :
      (z : P2) ∈ frontier T ↔ (e j z : P2) ∈ frontier T' := by
    have h₀ := C.outer_iff j ((C.chart j).symm z)
    simp only [Homeomorph.apply_symm_apply] at h₀
    exact (D.outer_in_disk_iff j z).trans (h₀.trans
      ((F.outer_iff j ((C.chart j).symm z)).symm.trans
        (E.outer_in_disk_iff j (e j z)).symm))
  have hinner (j : Fin 2) (z : D.disk j) :
      (z : P2) ∈ frontier S ↔ (e j z : P2) ∈ frontier S' := by
    have h₀ := C.inner_iff j ((C.chart j).symm z)
    simp only [Homeomorph.apply_symm_apply] at h₀
    exact (D.inner_in_disk_iff j z).trans (h₀.trans
      ((F.inner_iff j ((C.chart j).symm z)).symm.trans
        (E.inner_in_disk_iff j (e j z)).symm))
  obtain ⟨G, hG, hG₀, hG₁⟩ := Homeomorph.exists_union_finitePL
    (e 0) (e 1) (he 0) (he 1) hcross hagree
  let H := (Homeomorph.setCongr D.disk_cover.symm).trans
    (G.trans (Homeomorph.setCongr E.disk_cover))
  refine ⟨H, hG.setCongr D.disk_cover E.disk_cover, ?_, ?_⟩
  · intro z
    rcases D.disk_cover.symm.subset z.property with hz | hz
    · change (z : P2) ∈ frontier T ↔ (G ⟨z, _⟩ : P2) ∈ frontier T'
      rw [hG₀ ⟨z, hz⟩]
      exact houter 0 ⟨z, hz⟩
    · change (z : P2) ∈ frontier T ↔ (G ⟨z, _⟩ : P2) ∈ frontier T'
      rw [hG₁ ⟨z, hz⟩]
      exact houter 1 ⟨z, hz⟩
  · intro z
    rcases D.disk_cover.symm.subset z.property with hz | hz
    · change (z : P2) ∈ frontier S ↔ (G ⟨z, _⟩ : P2) ∈ frontier S'
      rw [hG₀ ⟨z, hz⟩]
      exact hinner 0 ⟨z, hz⟩
    · change (z : P2) ∈ frontier S ↔ (G ⟨z, _⟩ : P2) ∈ frontier S'
      rw [hG₁ ⟨z, hz⟩]
      exact hinner 1 ⟨z, hz⟩

end PoincareConjecture.M76.Dehn
