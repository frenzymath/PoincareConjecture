import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.MarkedCollarCorrection











set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology
open PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "A2" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem OriginalFiniteCollarModel.exists_proper_disk_boundary_correction
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (M : OriginalFiniteCollarModel e R)
    {B S₀ S₁ Q A₀ A₁ : Set (M.vertices → ℝ × V3)}
    (hB : IsFinitePLBallPair P2 B S₀) (hBR : B ⊆ M.complex.space)
    (a₀ : A2 ≃ₜ A₀) (a₁ : A2 ≃ₜ A₁)
    (ha₀ : a₀.IsFinitePL) (ha₁ : a₁.IsFinitePL)
    (hA₀ : A₀ ⊆ M.boundary.space) (hA₁ : A₁ ⊆ M.boundary.space)
    (h₀inner : annulusDepthImage a₀ 1 = S₀)
    (h₁inner : annulusDepthImage a₁ 1 = S₁)
    (h₀outer : annulusDepthImage a₀ (-1) = Q)
    (h₁outer : annulusDepthImage a₁ (-1) = Q) :
    ∃ Bnew : Set (M.vertices → ℝ × V3), IsFinitePLBallPair P2 Bnew S₁ ∧
      Bnew ⊆ M.complex.space ∧ Bnew ∩ M.boundary.space = S₁ := by
  let E := M.collarVertices → ℝ × V3
  let F := M.vertices → ℝ × V3
  let L := M.collarBase
  let HB := M.collarHomeomorph
  let c := M.collar
  have hHB := M.collarHomeomorph_isFinitePL
  have hc := M.collar_pl
  have hci := M.collar_injective
  have hcR := M.collar_inside
  have hbase := M.collar_zero
  have hfront := M.collar_boundary
  obtain ⟨D, H, hH, hDK, hDA, hHboundary, hclear⟩ := M.exists_inward_compression
  obtain ⟨U₀, u₀, hU₀, hu₀, hu₀val⟩ := exists_marked_annulus_lift HB hHB a₀ ha₀ hA₀
  obtain ⟨U₁, u₁, hU₁, hu₁, hu₁val⟩ := exists_marked_annulus_lift HB hHB a₁ ha₁ hA₁
  have hu₀L (p : A2) : (u₀ p : E) ∈ L.space := hU₀ (u₀ p).property
  have hu₁L (p : A2) : (u₁ p : E) ∈ L.space := hU₁ (u₁ p).property
  obtain ⟨T₀, b₀, hb₀, hb₀val⟩ := exists_correction_annulus_graph hc hci hU₀ u₀ hu₀ true
  obtain ⟨T₁, b₁, hb₁, hb₁val⟩ := exists_correction_annulus_graph hc hci hU₁ u₁ hu₁ false
  obtain ⟨f, hf, hfval⟩ := hH
  have hfi : InjOn f M.complex.space := by
    intro x hx y hy hxy
    have hh : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hfval ⟨x, hx⟩).trans (hxy.trans (hfval ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  let B₀ := f '' B
  let S' := f '' S₀
  let Q' := annulusDepthImage b₀ (-1)
  have hB₀ : IsFinitePLBallPair P2 B₀ S' := hB.image_of_subset hf hBR hfi
  have hB₀D : B₀ ⊆ D := by
    rintro z ⟨x, hx, rfl⟩
    rw [← hfval ⟨x, hBR hx⟩]
    exact (H ⟨x, hBR hx⟩).property
  have hhalf (p : A2) : M.collar ((u₀ p : E), (1 / 2 : ℝ)) = f (a₀ p) := by
    rw [hu₀val]
    have hh := hHboundary (HB.symm ⟨a₀ p, hA₀ (a₀ p).property⟩)
    rw [hfval] at hh
    simpa only [HB, Homeomorph.apply_symm_apply] using hh.symm
  have hzero (p : A2) : M.collar ((u₁ p : E), 0) = a₁ p := by
    rw [hu₁val, hbase]
    exact congrArg Subtype.val (HB.apply_symm_apply _)
  have hupperInner : annulusDepthImage b₀ 1 = S' := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      change depth 8 (p : P2) = 1 at hp
      refine ⟨a₀ p, h₀inner.subset ⟨p, hp, rfl⟩, ?_⟩
      change f (a₀ p) = (b₀ p : F)
      rw [hb₀val]
      have hh : annulusCorrectionHeight true p = (1 / 2 : ℝ) := by
        simp only [annulusCorrectionHeight, if_true, hp]
        norm_num
      rw [hh, hhalf]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨p, hp, hpx⟩ := h₀inner.symm.subset hx
      change depth 8 (p : P2) = 1 at hp
      refine ⟨p, hp, ?_⟩
      change (b₀ p : F) = f x
      change (a₀ p : F) = x at hpx
      rw [hb₀val]
      have hh : annulusCorrectionHeight true p = (1 / 2 : ℝ) := by
        simp only [annulusCorrectionHeight, if_true, hp]
        norm_num
      rw [hh, hhalf, hpx]
  have hlowerInner : annulusDepthImage b₁ 1 = S₁ := by
    have hv (p : A2) (hp : depth 8 (p : P2) = 1) : (b₁ p : F) = a₁ p := by
      rw [hb₁val]
      have hh : annulusCorrectionHeight false p = 0 := by
        simp only [annulusCorrectionHeight, Bool.false_eq_true, if_false, hp]
        norm_num
      rw [hh, hzero]
    rw [← h₁inner]
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, (hv p hp).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, hv p hp⟩
  have houterImages : annulusDepthImage b₁ (-1) = Q' := by
    have hvalues (p q : A2) (hp : depth 8 (p : P2) = -1)
        (hq : depth 8 (q : P2) = -1) (hpq : (a₀ p : F) = a₁ q) :
        (b₀ p : F) = b₁ q := by
      rw [hb₀val, hb₁val]
      apply (correction_annulus_graph_eq_iff hci
        (fun p ↦ (u₀ p : E)) (fun q ↦ (u₁ q : E)) hu₀L hu₁L p q).mpr
      refine ⟨?_, hp, hq⟩
      rw [hu₀val, hu₁val]
      exact congrArg (fun z : M.boundary.space ↦ (HB.symm z : E)) (Subtype.ext hpq)
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqQ : (a₁ q : F) ∈ Q := h₁outer.subset ⟨q, hq, rfl⟩
      obtain ⟨p, hp, hpq⟩ := h₀outer.symm.subset hqQ
      exact ⟨p, hp, hvalues p q hp hq hpq⟩
    · rintro ⟨p, hp, rfl⟩
      have hpQ : (a₀ p : F) ∈ Q := h₀outer.subset ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hqp⟩ := h₁outer.symm.subset hpQ
      exact ⟨q, hq, (hvalues p q hp hq hqp.symm).symm⟩
  have hBcontact : B₀ ∩ T₀ = S' := by
    apply Subset.antisymm
    · rintro z ⟨hzB, hzT⟩
      obtain ⟨p, hp⟩ := b₀.surjective ⟨z, hzT⟩
      have hv : (b₀ p : F) = z := congrArg Subtype.val hp
      have hzD : (b₀ p : F) ∈ D := hv.symm ▸ hB₀D hzB
      rw [hb₀val] at hzD
      have hdep := (correction_annulus_graph_clearance hclear
        (fun p ↦ (u₀ p : E)) hu₀L p).1.mp hzD
      exact hupperInner.subset ⟨p, hdep, hv⟩
    · intro z hz
      exact ⟨hB₀.1 hz, annulusDepthImage_subset b₀ 1 (hupperInner.symm.subset hz)⟩
  have hT₁off (z : F) (hz : z ∈ T₁) : z ∉ D := by
    obtain ⟨p, hp⟩ := b₁.surjective ⟨z, hz⟩
    have hv : (b₁ p : F) = z := congrArg Subtype.val hp
    rw [← hv, hb₁val]
    exact (correction_annulus_graph_clearance hclear
      (fun p ↦ (u₁ p : E)) hu₁L p).2
  have hgraphContact : T₀ ∩ T₁ = Q' := by
    apply Subset.antisymm
    · rintro z ⟨hz₀, hz₁⟩
      obtain ⟨p, hp⟩ := b₀.surjective ⟨z, hz₀⟩
      obtain ⟨q, hq⟩ := b₁.surjective ⟨z, hz₁⟩
      have hpz : (b₀ p : F) = z := congrArg Subtype.val hp
      have hqz : (b₁ q : F) = z := congrArg Subtype.val hq
      have hpq := hpz.trans hqz.symm
      rw [hb₀val, hb₁val] at hpq
      have hends := (correction_annulus_graph_eq_iff hci
        (fun p ↦ (u₀ p : E)) (fun q ↦ (u₁ q : E)) hu₀L hu₁L p q).mp hpq
      exact ⟨p, hends.2.1, hpz⟩
    · intro z hz
      exact ⟨annulusDepthImage_subset b₀ (-1) hz,
        annulusDepthImage_subset b₁ (-1) (houterImages.symm.subset hz)⟩
  have hballUpper : IsFinitePLBallPair P2 (B₀ ∪ T₀) Q' := by
    apply isFinitePLBallPair_attach_annulus_inner hB₀ hBcontact
      (by norm_num) (by norm_num) b₀ hb₀ ?_ (annulusDepthImage_subset b₀ (-1)) ?_
    · intro p
      rw [← hupperInner]
      exact (mem_annulusDepthImage_iff b₀ 1 p).symm
    · intro p
      exact (mem_annulusDepthImage_iff b₀ (-1) p).symm
  have hcontactLower : (B₀ ∪ T₀) ∩ T₁ = Q' := by
    apply Subset.antisymm
    · rintro z ⟨hzB | hzT, hz₁⟩
      · exact (hT₁off z hz₁ (hB₀D hzB)).elim
      · exact hgraphContact.subset ⟨hzT, hz₁⟩
    · intro z hz
      have hh := hgraphContact.symm.subset hz
      exact ⟨Or.inr hh.1, hh.2⟩
  have hball : IsFinitePLBallPair P2 ((B₀ ∪ T₀) ∪ T₁) S₁ := by
    apply isFinitePLBallPair_attach_annulus_outer hballUpper hcontactLower
      (by norm_num) (by norm_num) b₁ hb₁ ?_
      (hlowerInner ▸ annulusDepthImage_subset b₁ 1) ?_
    · intro p
      rw [← houterImages]
      exact (mem_annulusDepthImage_iff b₁ (-1) p).symm
    · intro p
      rw [← hlowerInner]
      exact (mem_annulusDepthImage_iff b₁ 1 p).symm
  have hT₀R : T₀ ⊆ M.complex.space := by
    intro z hz
    obtain ⟨p, hp⟩ := b₀.surjective ⟨z, hz⟩
    have hv : (b₀ p : F) = z := congrArg Subtype.val hp
    rw [← hv, hb₀val]
    exact hcR ⟨hu₀L p, (annulusCorrectionHeight_bounds true p).1⟩
  have hT₁R : T₁ ⊆ M.complex.space := by
    intro z hz
    obtain ⟨p, hp⟩ := b₁.surjective ⟨z, hz⟩
    have hv : (b₁ p : F) = z := congrArg Subtype.val hp
    rw [← hv, hb₁val]
    exact hcR ⟨hu₁L p, (annulusCorrectionHeight_bounds false p).1⟩
  refine ⟨(B₀ ∪ T₀) ∪ T₁, hball, ?_, ?_⟩
  · exact union_subset (union_subset (hB₀D.trans hDK) hT₀R) hT₁R
  · apply Subset.antisymm
    · rintro z ⟨(hzB | hz₀) | hz₁, hzfront⟩
      · exact (Set.disjoint_left.mp hDA (hB₀D hzB) hzfront).elim
      · obtain ⟨p, hp⟩ := b₀.surjective ⟨z, hz₀⟩
        have hv : (b₀ p : F) = z := congrArg Subtype.val hp
        rw [← hv, hb₀val] at hzfront
        exact ((correction_annulus_graph_mark hfront
          (fun p ↦ (u₀ p : E)) hu₀L p).1 hzfront).elim
      · obtain ⟨p, hp⟩ := b₁.surjective ⟨z, hz₁⟩
        have hv : (b₁ p : F) = z := congrArg Subtype.val hp
        rw [← hv, hb₁val] at hzfront
        have hdep := (correction_annulus_graph_mark hfront
          (fun p ↦ (u₁ p : E)) hu₁L p).2.mp hzfront
        exact hlowerInner.subset ⟨p, hdep, hv⟩
    · intro z hz
      refine ⟨hball.1 hz, ?_⟩
      exact hA₁ (annulusDepthImage_subset a₁ 1 (h₁inner.symm.subset hz))

end PoincareConjecture.M76
