import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionCollarExcision
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLTopFace

set_option autoImplicit false

open Set Geometry

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.excision_of_spherical_boundary_collar
    {B O s C b c d e q : Set (X × ℝ)} {D : Set X}
    (hdim : Module.finrank ℝ X = 3)
    (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (c ∪ d))
    (hO : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) O (c ∪ d))
    (hs : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (b ∪ d))
    (hC : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (b ∪ e))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (he : IsFinitePLBallPair (ℝ × ℝ) e q)
    (hbd : b ∩ d = q) (hbe : b ∩ e = q) (hcd : c ∩ d = q)
    (hsC : s ∩ C = b) (hsB : s ⊆ B) (hCB : C ⊆ B)
    (hBO : B ∩ O = c ∪ d) (hsO : s ∩ O = d) (hCO : C ∩ O ⊆ q)
    (hBsphere : B ⊆ frontier (D ×ˢ Icc (-1 : ℝ) 1))
    (hOsphere : O ⊆ frontier (D ×ˢ Icc (-1 : ℝ) 1))
    (hPtop : s ∪ C ⊆ interior D ×ˢ {(1 : ℝ)}) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure (B \ s)) (b ∪ c) := by
  let P := s ∪ C
  let S := frontier (D ×ˢ Icc (-1 : ℝ) 1)
  have hPB : P ⊆ B := union_subset hsB hCB
  have hPS : P ⊆ S := hPB.trans hBsphere
  have hPO : P ∩ O = d := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hxO⟩
      rcases hxP with hxs | hxC
      · exact hsO.subset ⟨hxs, hxO⟩
      · exact hd.1 (hCO ⟨hxC, hxO⟩)
    · intro x hx
      have hh := hsO.symm.subset hx
      exact ⟨Or.inl hh.1, hh.2⟩
  have hPc : P ∩ c ⊆ e := by
    rintro x ⟨hxP, hxc⟩
    have hxd : x ∈ d := hPO.subset ⟨hxP, hO.1 (Or.inl hxc)⟩
    exact he.1 (hcd.subset ⟨hxc, hxd⟩)
  have hs' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (d ∪ b) := by
    simpa only [union_comm] using hs
  have hC' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (e ∪ b) := by
    simpa only [union_comm] using hC
  have hdb : d ∩ b = q := (inter_comm _ _).trans hbd
  have heb : e ∩ b = q := (inter_comm _ _).trans hbe
  have hde : d ∩ e = q := by
    apply Subset.antisymm
    · rintro x ⟨hxd, hxe⟩
      have hxb := hsC.subset ⟨hs.1 (Or.inr hxd), hC.1 (Or.inr hxe)⟩
      exact hbd.subset ⟨hxb, hxd⟩
    · exact subset_inter hd.1 he.1
  have hP : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) P (d ∪ e) :=
    hs'.union_of_ball_disk_attachment hC' hd he hb hdb heb hsC
  have hP' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) P (e ∪ d) := by
    simpa only [union_comm] using hP
  have hW : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (P ∪ O) (e ∪ c) :=
    hP'.union_of_ball_disk_attachment hO he hc hd
      ((inter_comm _ _).trans hde) hcd hPO
  have hmodeldim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ X := by
    simp [Module.finrank_prod, hdim]
  let j : B → S := fun x => ⟨x, hBsphere x.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hint (x : B) (hx : (x : X × ℝ) ∈ P \ e) :
      x ∈ interior ((Subtype.val : B → X × ℝ) ⁻¹' P) := by
    have hxD : (x : X × ℝ).1 ∈ interior D := (hPtop hx.1).1
    have hxtop : (x : X × ℝ).2 = 1 := (hPtop hx.1).2
    by_cases hxd : (x : X × ℝ) ∈ d
    · have hxc : (x : X × ℝ) ∉ c := fun hc' => hx.2 (he.1 (hcd.subset ⟨hc', hxd⟩))
      have hxW : j x ∈ interior ((Subtype.val : S → X × ℝ) ⁻¹' (P ∪ O)) :=
        hW.mem_interior_preimage_cylinder hmodeldim (union_subset hPS hOsphere)
          (j x) ⟨Or.inl hx.1, fun h => h.elim hx.2 hxc⟩ hxD hxtop
      let V := interior ((Subtype.val : S → X × ℝ) ⁻¹' (P ∪ O)) \
        (Subtype.val : S → X × ℝ) ⁻¹' c
      have hV : IsOpen V := isOpen_interior.sdiff
        (hc.isCompact.isClosed.preimage continuous_subtype_val)
      have hsub : j ⁻¹' V ⊆ (Subtype.val : B → X × ℝ) ⁻¹' P := by
        intro y hy
        rcases interior_subset hy.1 with hyP | hyO
        · exact hyP
        · rcases hBO.subset ⟨y.property, hyO⟩ with hyc | hyd
          · exact (hy.2 hyc).elim
          · exact Or.inl (hs.1 (Or.inr hyd))
      exact interior_maximal hsub (hV.preimage hj) ⟨hxW, hxc⟩
    · have hxP : j x ∈ interior ((Subtype.val : S → X × ℝ) ⁻¹' P) :=
        hP.mem_interior_preimage_cylinder hmodeldim hPS (j x)
          ⟨hx.1, fun h => h.elim hxd hx.2⟩ hxD hxtop
      exact preimage_interior_subset_interior_preimage hj hxP
  exact hB.excision_of_boundary_collar hs hC hb hd he hbd hbe hsC hsB hCB hPc hint

end Set
