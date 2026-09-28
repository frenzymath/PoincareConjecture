import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveClosedPieces
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabLevelCoverage
import PoincareConjecture.Proofs.M76.Mathlib.ClosedComplementHeightSigns











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem AlexanderCollarSlab.ordinary_retained_mem_both_height_closures
    {S s s' d rim TX TY : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β t : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {x | A x = 0})
    (hsplit : M.collar ∩ s = TX ∪ TY) (hdisj : Disjoint TX TY)
    (hrim : IsClosed rim)
    (hY : ∀ w : {w : E × ℝ | w.1 ∈ S ∩ {x | A x = 0} ∧
        w.2 ∈ Icc 0 (M.upper w.1)},
      (M.chart w : E) ∈ TY ↔ (w : E × ℝ).1 ∈ rim)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ M.residual, H x = x)
    (ht : t < β) (hroof : ∀ x ∈ rim, t < M.upper x)
    (F : (TX ∪ (M.residual ∩ s) : Set E) ≃ₜ
      ((H '' TX) ∪ (M.residual ∩ s) : Set E))
    (hFA : ∀ x, A (F x) = A x)
    (hsource : ∀ x ∈ S, A x ∈ Ioc (0 : ℝ) t →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y})) :
    ∀ x ∈ (H '' TX) ∪ (M.residual ∩ s), A x ∈ Ioc (0 : ℝ) t →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have hXs : TX ⊆ s :=
    (subset_union_left.trans hsplit.symm.subset).trans inter_subset_right
  have hYs : TY ⊆ s :=
    (subset_union_right.trans hsplit.symm.subset).trans inter_subset_right
  have hYT : TY ⊆ M.collar :=
    (subset_union_right.trans hsplit.symm.subset).trans inter_subset_left
  have hRs : TX ∪ (M.residual ∩ s) ⊆ s := union_subset hXs inter_subset_right
  have hTY : IsClosed TY := (M.isCompact_piece_of_closed_base hrim hYT hY).isClosed
  let Z := (TY ∪ s') ∩ {x | A x ∈ Icc (0 : ℝ) β}
  have hZ : IsClosed Z := (hTY.union hs').inter
    (isClosed_Icc.preimage A.continuous_of_finiteDimensional)
  have hcover : ((TX ∪ (M.residual ∩ s)) ∩ {x | A x ∈ Icc (0 : ℝ) β}) ∪ Z =
      S ∩ {x | A x ∈ Icc (0 : ℝ) β} := by
    ext x
    constructor
    · rintro (⟨hxR, hxA⟩ | ⟨hxY | hxs', hxA⟩)
      · exact ⟨hsS (hRs hxR), hxA⟩
      · exact ⟨hsS (hYs hxY), hxA⟩
      · exact ⟨hunion.subset (Or.inr hxs'), hxA⟩
    · intro hx
      rcases hunion.symm.subset hx.1 with hxs | hxs'
      · have hxTR := (cut_slab_level_eq hsS M.cover hx.2).symm.subset ⟨hxs, rfl⟩
        rcases hxTR.1 with hxT | hxR
        · rcases hsplit.subset hxT with hxX | hxY
          · exact Or.inl ⟨Or.inl hxX, hx.2⟩
          · exact Or.inr ⟨Or.inl hxY, hx.2⟩
        · exact Or.inl ⟨Or.inr hxR, hx.2⟩
      · exact Or.inr ⟨Or.inr hxs', hx.2⟩
  have htarget : (H '' TX) ∪ (M.residual ∩ s) ⊆ H '' (s ∪ d) := by
    rintro x (hxX | hxR)
    · exact image_mono (hXs.trans subset_union_left) hxX
    · exact ⟨x, Or.inl hxR.2, hfix x hxR.1⟩
  intro x hx hxA
  let y := F.symm ⟨x, hx⟩
  have hFy : (F y : E) = x := congrArg Subtype.val (F.apply_symm_apply _)
  have hyA : A y ∈ Ioc (0 : ℝ) t :=
    ((hFA y).symm.trans (congrArg A hFy)).symm ▸ hxA
  have hyZ : (y : E) ∉ Z := by
    intro hy
    rcases hy.1 with hyY | hys'
    · rcases y.property with hyX | hyR
      · exact disjoint_left.mp hdisj hyX hyY
      · let w := M.chart.symm ⟨y, hYT hyY⟩
        have hw : (M.chart w : E) = y := congrArg Subtype.val (M.chart.apply_symm_apply _)
        have hwrim := (hY w).mp (hw.symm ▸ hyY)
        have htop := (M.roof_contact w).mp (hw.symm ▸ hyR.1)
        have hAy : A y = M.upper (w : E × ℝ).1 :=
          (congrArg A hw).symm.trans ((M.height w).trans htop)
        exact ((hroof _ hwrim).trans_eq hAy.symm).not_ge hyA.2
    · exact hyA.1.ne' (hcut ⟨hRs y.property, hys'⟩)
  obtain ⟨hlo, hhi⟩ := hsource y (hsS (hRs y.property)) hyA
  have hsigns := F.mem_both_height_closures_of_closed_band_cover A A
    A.continuous_of_finiteDimensional hFA hZ hcover y hyZ hyA.1 (hyA.2.trans_lt ht) hlo hhi
  rw [hFy] at hsigns
  exact ⟨closure_mono (inter_subset_inter_left _ htarget) hsigns.1,
    closure_mono (inter_subset_inter_left _ htarget) hsigns.2⟩

end Geometry
