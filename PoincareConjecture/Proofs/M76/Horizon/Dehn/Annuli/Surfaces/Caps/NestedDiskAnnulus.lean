import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus
import PoincareConjecture.Proofs.M76.Mathlib.NestedPLBallRelativeInterior

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_square_annulus_nested_ball_pairs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b d q : Set E} (ha : IsFinitePLBallPair P2 a b)
    (hd : IsFinitePLBallPair P2 d q) (had : a ⊆ d \ q) :
    ∃ H : Ann ≃ₜ (d \ (a \ b) : Set E), H.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (H z : E) ∈ q) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (H z : E) ∈ b) := by
  obtain ⟨hqd, C, hC, hcv, hne, e, he, heb⟩ := hd
  have hecopy := he
  obtain ⟨f, hf, hef⟩ := hecopy
  obtain ⟨g, hg, heg⟩ := he.symm
  have hgf : LeftInvOn g f d := by
    intro x hx
    rw [← hef ⟨x, hx⟩, ← heg, e.symm_apply_apply]
  have hfg : LeftInvOn f g C := by
    intro y hy
    rw [← heg ⟨y, hy⟩, ← hef, e.apply_symm_apply]
  have hfC : f '' d = C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property,
        (hef (e.symm ⟨y, hy⟩)).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))⟩
  have hgD : g '' C = d := by
    rw [← hfC, image_image]
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      change g (f x) ∈ d
      rwa [hgf hx]
    · intro x hx
      exact ⟨_, hx, hgf hx⟩
  have hgC (y : P2) (hy : y ∈ C) : g y ∈ d := hgD.subset (mem_image_of_mem g hy)
  have hmember (B : Set E) (hBd : B ⊆ d) (y : P2) (hy : y ∈ C) :
      g y ∈ B ↔ y ∈ f '' B := by
    constructor
    · intro hB
      exact ⟨g y, hB, hfg hy⟩
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy, hgf (hBd hx)]
      exact hx
  have hfq : f '' q = frontier C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hqd hx⟩]
      exact (heb ⟨x, hqd hx⟩).mp hx
    · intro hy
      have hyC := hC.isClosed.frontier_subset hy
      refine ⟨g y, ?_, hfg hyC⟩
      apply (heb ⟨g y, hgC y hyC⟩).mpr
      rwa [hef, hfg hyC]
  have hfa := ha.image_of_subset hf (had.trans sdiff_subset) hgf.injOn
  have hinside : f '' a ⊆ interior C := by
    rintro y ⟨x, hx, rfl⟩
    have hxC : f x ∈ C := hfC.subset (mem_image_of_mem f (had hx).1)
    by_contra hnot
    have hfr : f x ∈ frontier C := ⟨subset_closure hxC, hnot⟩
    exact (had hx).2 ((heb ⟨x, (had hx).1⟩).mpr (by rwa [hef]))
  have hCpair : IsFinitePLBallPair P2 C (frontier C) := by
    obtain ⟨J, hJ, hJC, _⟩ := hg
    exact isFinitePLBallPair_of_compact_convex hC hcv hne J hJ hJC
  have hfa' : IsFinitePLBallPair P2 (f '' a) (frontier (f '' a)) := by
    rw [hfa.frontier_eq_of_finrank_eq rfl]
    exact hfa
  obtain ⟨A, hA, houter, hinner⟩ := exists_square_annulus_nested_disks hfa' hCpair hinside
    (by norm_num : (0 : ℝ) < 1) (by norm_num : 2 * (1 : ℝ) < 8)
  obtain ⟨p, hp, hpA⟩ := hA
  have hpC (z : Ann) : p z ∈ C := (hpA z).symm ▸ (A z).property.1
  have hpImage : p '' Ann = C \ interior (f '' a) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hpA ⟨z, hz⟩]
      exact (A ⟨z, hz⟩).property
    · intro hy
      refine ⟨A.symm ⟨y, hy⟩, (A.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hpA, A.apply_symm_apply]
  have hback : g '' (C \ interior (f '' a)) = d \ (a \ b) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hgC y hy.1, ?_⟩
      intro hx
      apply hy.2
      rw [hfa.interior_eq_sdiff_of_finrank_eq rfl]
      exact ⟨(hmember a (had.trans sdiff_subset) y hy.1).mp hx.1,
        fun hyb ↦ hx.2 ((hmember b (ha.1.trans (had.trans sdiff_subset)) y hy.1).mpr hyb)⟩
    · intro hx
      have hyC : f x ∈ C := hfC.subset (mem_image_of_mem f hx.1)
      refine ⟨f x, ⟨hyC, ?_⟩, hgf hx.1⟩
      intro hy
      rw [hfa.interior_eq_sdiff_of_finrank_eq rfl] at hy
      apply hx.2
      have hxA := (hmember a (had.trans sdiff_subset) (f x) hyC).mpr hy.1
      rw [hgf hx.1] at hxA
      refine ⟨hxA, ?_⟩
      exact fun hxb ↦ hy.2 (mem_image_of_mem f hxb)
  have hcomp : FinitePiecewiseAffineOn (g ∘ p) Ann :=
    hg.comp hp (fun z hz ↦ hpC ⟨z, hz⟩)
  have hinj : InjOn (g ∘ p) Ann := by
    intro x hx y hy hxy
    have hpEq := hfg.injOn (hpC ⟨x, hx⟩) (hpC ⟨y, hy⟩) hxy
    have heq : A ⟨x, hx⟩ = A ⟨y, hy⟩ :=
      Subtype.ext ((hpA ⟨x, hx⟩).trans (hpEq.trans (hpA ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (A.injective heq)
  obtain ⟨B, hB, hBval⟩ := hcomp.exists_homeomorph_image hinj
  have hcarrier : (g ∘ p) '' Ann = d \ (a \ b) :=
    (image_image g p Ann).symm.trans ((congrArg (fun X ↦ g '' X) hpImage).trans hback)
  let H := B.trans (Homeomorph.setCongr hcarrier)
  refine ⟨H, hB.setCongr rfl hcarrier, ?_, ?_⟩
  · intro z
    change depth 8 (z : P2) = -1 ↔ (B z : E) ∈ q
    rw [hBval, Function.comp_apply, hmember q hqd _ (hpC z), hfq, ← hpA]
    exact houter z
  · intro z
    change depth 8 (z : P2) = 1 ↔ (B z : E) ∈ b
    rw [hBval, Function.comp_apply, hmember b (ha.1.trans (had.trans sdiff_subset)) _ (hpC z),
      ← hfa.frontier_eq_of_finrank_eq rfl, ← hpA]
    exact hinner z

end PoincareConjecture.M76.Dehn
