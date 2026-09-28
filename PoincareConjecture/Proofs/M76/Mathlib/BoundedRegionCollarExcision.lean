import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionCollarCompression
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionCompressionGluing
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBoundaryCollarTopology

set_option autoImplicit false

open Set Geometry

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.excision_of_boundary_collar
    {B s C b c d e q : Set X}
    (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (c ∪ d))
    (hs : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (b ∪ d))
    (hC : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (b ∪ e))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (he : IsFinitePLBallPair (ℝ × ℝ) e q)
    (hbd : b ∩ d = q) (hbe : b ∩ e = q) (hsC : s ∩ C = b)
    (hsB : s ⊆ B) (hCB : C ⊆ B) (hPc : (s ∪ C) ∩ c ⊆ e)
    (hint : ∀ x : B, (x : X) ∈ (s ∪ C) \ e →
      x ∈ interior ((Subtype.val : B → X) ⁻¹' (s ∪ C))) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure (B \ s)) (b ∪ c) := by
  let P := s ∪ C
  let R := closure (B \ P)
  have hPB : P ⊆ B := union_subset hsB hCB
  have hRB : R ⊆ B := closure_minimal sdiff_subset hB.isCompact.isClosed
  have hR : IsCompact R := hB.isCompact.of_isClosed_subset isClosed_closure hRB
  have hwhole : P ∪ R = B := by
    apply Subset.antisymm (union_subset hPB hRB)
    intro x hx
    by_cases hxP : x ∈ P
    · exact Or.inl hxP
    · exact Or.inr (subset_closure ⟨hx, hxP⟩)
  have hPR : P ∩ R ⊆ e := by
    rintro x ⟨hxP, hxR⟩
    by_contra hxe
    let z : B := ⟨x, hPB hxP⟩
    have hzint := hint z ⟨hxP, hxe⟩
    have hzcl : z ∈ closure ((Subtype.val : B → X) ⁻¹' (B \ P)) := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
        image_preimage_eq_of_subset (by simp)]
      exact hxR
    obtain ⟨y, hyP, hyout⟩ := mem_closure_iff.mp hzcl
      (interior ((Subtype.val : B → X) ⁻¹' P)) isOpen_interior hzint
    have hyin : y ∈ (Subtype.val : B → X) ⁻¹' P := interior_subset hyP
    exact hyout.2 hyin
  obtain ⟨H, hH, hHe, hHd, _⟩ := hs.exists_boundary_collar_compression hC hb hd he
    hbd hbe hsC
  have hfix (x : P) (hxR : (x : X) ∈ R) : (H x : X) = x :=
    hHe ⟨x, hPR ⟨x.property, hxR⟩⟩
  have hcopy := hB
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKB, _⟩, _⟩, _⟩ := hcopy
  obtain ⟨G, hG, hGP, hGR⟩ := H.exists_finitePL_union_id_of_fixed_overlap hH hR
    subset_union_right hfix K hK (hKB.trans hwhole.symm)
  have hcsource : c ⊆ P ∪ R := fun _ hx => hwhole.symm.subset (hB.1 (Or.inl hx))
  have hGc (x : c) : (G ⟨x, hcsource x.property⟩ : X) = x := by
    by_cases hxP : (x : X) ∈ P
    · exact (hGP ⟨x, hxP⟩).trans (hHe ⟨x, hPc ⟨hxP, x.property⟩⟩)
    · exact hGR ⟨x, (hcsource x.property).resolve_left hxP⟩
  have hctarget : c ⊆ C ∪ R := by
    intro x hx
    have hval : (G ⟨x, hcsource hx⟩ : X) = x := hGc ⟨x, hx⟩
    exact hval ▸ (G ⟨x, hcsource hx⟩).property
  have hciff (x : (P ∪ R : Set X)) : (x : X) ∈ c ↔ (G x : X) ∈ c := by
    constructor
    · intro hx
      exact (hGc ⟨x, hx⟩).symm ▸ hx
    · intro hx
      have heq : G ⟨G x, hcsource hx⟩ = G x := Subtype.ext (hGc ⟨G x, hx⟩)
      exact congrArg Subtype.val (G.injective heq) ▸ hx
  have hdiff (x : (P ∪ R : Set X)) : (x : X) ∈ d ↔ (G x : X) ∈ b := by
    constructor
    · intro hx
      have hxP : (x : X) ∈ P := Or.inl (hs.1 (Or.inr hx))
      rw [hGP ⟨x, hxP⟩]
      exact (hHd ⟨x, hxP⟩).mp hx
    · intro hx
      let y : C := ⟨G x, hC.1 (Or.inl hx)⟩
      let z : P := H.symm y
      have hz : (H z : X) = (G x : X) := congrArg Subtype.val (H.apply_symm_apply y)
      have hGz : G ⟨z, Or.inl z.property⟩ = G x := Subtype.ext ((hGP z).trans hz)
      have hzx : (z : X) = x := congrArg Subtype.val (G.injective hGz)
      exact hzx ▸ (hHd z).mpr (hz.symm ▸ hx)
  have hball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (C ∪ R) (b ∪ c) := by
    have hB' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (P ∪ R) (c ∪ d) := hwhole.symm ▸ hB
    apply hB'.of_homeomorph
      (union_subset (fun _ hx => Or.inl (hC.1 (Or.inl hx))) hctarget) G.symm hG.symm
    intro y
    have hc' := hciff (G.symm y)
    have hd' := hdiff (G.symm y)
    have hGy : (G (G.symm y) : X) = y := congrArg Subtype.val (G.apply_symm_apply y)
    change (G.symm y : X) ∈ c ↔ (G (G.symm y) : X) ∈ c at hc'
    change (G.symm y : X) ∈ d ↔ (G (G.symm y) : X) ∈ b at hd'
    rw [hGy] at hc' hd'
    change ((y : X) ∈ b ∨ (y : X) ∈ c) ↔
      ((G.symm y : X) ∈ c ∨ (G.symm y : X) ∈ d)
    tauto
  have htarget : C ∪ R = closure (B \ s) := by
    apply Subset.antisymm
    · apply union_subset
      · have hCsub : C \ b ⊆ B \ s := by
          rintro x ⟨hxC, hxb⟩
          exact ⟨hCB hxC, fun hxs => hxb (hsC.subset ⟨hxs, hxC⟩)⟩
        calc
          C = closure (C \ b) :=
            (hC.closure_sdiff_of_subset_boundary subset_union_left).symm
          _ ⊆ closure (B \ s) := closure_mono hCsub
      · exact closure_mono (sdiff_subset_sdiff_right subset_union_left)
    · apply closure_minimal _ (hC.isCompact.isClosed.union isClosed_closure)
      rintro x ⟨hxB, hxs⟩
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · exact Or.inr (subset_closure ⟨hxB, fun hxP => hxP.elim hxs hxC⟩)
  exact htarget ▸ hball

end Set
