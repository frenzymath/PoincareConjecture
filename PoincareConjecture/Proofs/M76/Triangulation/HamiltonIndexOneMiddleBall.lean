import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneShellBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (ℝ × ℝ)
local notation "W" => (ℝ × V2)

def squareMiddleBlock : Set W := Icc (-1) 1 ×ˢ closedBall 0 (3 / 2)

private theorem middle_ballPair :
    IsFinitePLBallPair W squareMiddleBlock (squareInnerAnnulus ∪ squareAttachingDisks) := by
  have hbase := CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 3 / 2)
  have hspace : CoordinateHalfBoxes.base (3 / 2) = closedBall (0 : V2) (3 / 2) := by
    ext v
    simp only [CoordinateHalfBoxes.base, mem_prod, mem_Icc, mem_closedBall_zero_iff,
      Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
  have hboundary : CoordinateHalfBoxes.baseBoundary (3 / 2) = sphere (0 : V2) (3 / 2) := by
    rw [← hbase.frontier_eq_of_finrank_eq rfl, hspace, frontier_closedBall _ (by norm_num)]
  have h := (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod hbase
  rw [hspace, hboundary, union_comm] at h
  exact h

private theorem attaching_identity_finitePL :
    FinitePiecewiseAffineOn (id : W → W) squareAttachingDisks := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := middle_ballPair
  let A : W →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ V2).toAffineMap
  obtain ⟨L, hL, hLs⟩ := K.exists_finite_affineLevel_complex hK A (-1)
  obtain ⟨U, hU, hUs⟩ := K.exists_finite_affineLevel_complex hK A 1
  have hcover : L.space ∪ U.space = squareAttachingDisks := by
    rw [hLs, hUs, hKs]
    ext x
    change ((x ∈ squareMiddleBlock ∧ x.1 = -1) ∨
      (x ∈ squareMiddleBlock ∧ x.1 = 1)) ↔
      (x.1 ∈ ({-1, 1} : Set ℝ) ∧ x.2 ∈ closedBall (0 : V2) (3 / 2))
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (⟨hx, hm⟩ | ⟨hx, hp⟩)
      · exact ⟨Or.inl hm, hx.2⟩
      · exact ⟨Or.inr hp, hx.2⟩
    · rintro ⟨hm | hp, hv⟩
      · exact Or.inl ⟨⟨by rw [hm]; norm_num, hv⟩, hm⟩
      · exact Or.inr ⟨⟨by rw [hp]; norm_num, hv⟩, hp⟩
  have h := finitePiecewiseAffineOn_union
    (L.affineOnFaces_affine (ContinuousAffineMap.id ℝ W) |>.finitePiecewiseAffineOn hL)
    (U.affineOnFaces_affine (ContinuousAffineMap.id ℝ W) |>.finitePiecewiseAffineOn hU)
  exact hcover ▸ h

private theorem inner_inter_attaching : squareInnerAnnulus ∩ squareAttachingDisks = squareRims := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2.1, hx.1.2⟩
  · intro hx
    have hs : x.1 = -1 ∨ x.1 = 1 := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hx.1
    have hi : x.1 ∈ Icc (-1 : ℝ) 1 := by
      rcases hs with hs | hs <;> rw [hs] <;> norm_num
    exact ⟨⟨hi, hx.2⟩, ⟨hx.1, sphere_subset_closedBall hx.2⟩⟩

private theorem attaching_frontier : squareAttachingDisks ⊆ frontier squareBlock := by
  intro x hx
  have hs : x.1 = -1 ∨ x.1 = 1 := by
    simpa only [mem_insert_iff, mem_singleton_iff] using hx.1
  have hi : x.1 ∈ Icc (-1 : ℝ) 1 := by
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  have hv : ‖x.2‖ ≤ (3 / 2 : ℝ) := mem_closedBall_zero_iff.mp hx.2
  refine ⟨subset_closure ⟨hi, mem_closedBall_zero_iff.mpr (by linarith)⟩, ?_⟩
  intro hxi
  rw [squareBlock, interior_prod_eq, interior_Icc] at hxi
  rcases hs with hs | hs
  · exact (lt_irrefl (-1 : ℝ)) (hs ▸ hxi.1.1)
  · exact (lt_irrefl (1 : ℝ)) (hs ▸ hxi.1.2)

theorem exists_marked_middle_ball {B T : Set W}
    (hB : IsFinitePLBallPair W B (T ∪ squareAttachingDisks))
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x) :
    ∃ phi : squareMiddleBlock ≃ₜ B, phi.IsFinitePL ∧
      (∀ x : squareInnerAnnulus, ∀ hx : (x : W) ∈ squareMiddleBlock,
        (phi ⟨x, hx⟩ : W) = tau x) ∧
      (∀ x : squareAttachingDisks, ∀ hx : (x : W) ∈ squareMiddleBlock,
        (phi ⟨x, hx⟩ : W) = x) ∧
      ∀ x : squareMiddleBlock,
        (x : W) ∈ squareInnerAnnulus ↔ (phi x : W) ∈ T := by
  have hTcaps : T ∩ squareAttachingDisks = squareRims := by
    ext x
    constructor
    · intro hx
      exact hrims ▸ ⟨hx.1, attaching_frontier hx.2⟩
    · intro hx
      have h := hrims.symm ▸ hx
      exact ⟨h.1, hx.1, sphere_subset_closedBall hx.2⟩
  let d := Homeomorph.refl squareAttachingDisks
  have hd : d.IsFinitePL := ⟨id, attaching_identity_finitePL, fun _ => rfl⟩
  have hover (x : squareInnerAnnulus) : (x : W) ∈ squareAttachingDisks ↔
      (tau x : W) ∈ squareAttachingDisks := by
    constructor
    · intro hx
      have hr : (x : W) ∈ squareRims := inner_inter_attaching ▸ ⟨x.property, hx⟩
      rwa [hfix x hr]
    · intro hx
      have hr : (tau x : W) ∈ squareRims := hTcaps ▸ ⟨(tau x).property, hx⟩
      have hp := inner_inter_attaching.symm ▸ hr
      let y : squareInnerAnnulus := ⟨tau x, hp.1⟩
      have heq : tau y = tau x := Subtype.ext (hfix y hr)
      have hval : (x : W) = tau x := (congrArg Subtype.val (tau.injective heq)).symm
      rwa [hval]
  obtain ⟨e, he, hei, hec⟩ := Homeomorph.exists_union_finitePL tau d htau hd hover
    (fun x hxI hxC => hfix ⟨x, hxI⟩ (inner_inter_attaching ▸ ⟨hxI, hxC⟩))
  obtain ⟨phi, hphi, hbound, _⟩ := middle_ballPair.exists_extension hB e he
  have hinner (x : squareInnerAnnulus) (hx : (x : W) ∈ squareMiddleBlock) :
      (phi ⟨x, hx⟩ : W) = tau x := by
    have h := congrArg Subtype.val (hbound ⟨x, Or.inl x.property⟩)
    exact h.trans (hei x)
  refine ⟨phi, hphi, hinner, ?_, ?_⟩
  · intro x hx
    have h := congrArg Subtype.val (hbound ⟨x, Or.inr x.property⟩)
    exact h.trans (hec x)
  · intro x
    constructor
    · intro hx
      rw [hinner ⟨x, hx⟩ x.property]
      exact (tau ⟨x, hx⟩).property
    · intro hx
      let y := tau.symm ⟨phi x, hx⟩
      have hyM : (y : W) ∈ squareMiddleBlock := ⟨y.property.1,
        sphere_subset_closedBall y.property.2⟩
      have hyphi : phi ⟨y, hyM⟩ = phi x := by
        apply Subtype.ext
        rw [hinner y hyM]
        exact congrArg Subtype.val (tau.apply_symm_apply ⟨phi x, hx⟩)
      have heq : (y : W) = x := congrArg Subtype.val (phi.injective hyphi)
      exact heq ▸ y.property

end PoincareConjecture.M76.HamiltonIndexOne
