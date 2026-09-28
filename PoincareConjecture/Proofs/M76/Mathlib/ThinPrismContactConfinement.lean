import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set

namespace CoordinateHalfBoxes

variable {E : Type*} [TopologicalSpace E] [T2Space E]






theorem exists_thin_prism_contact_subset
    {F G : ((ℝ × ℝ) × ℝ) → E} {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hF : ContinuousOn F (box R)) (hG : ContinuousOn G (box S))
    {U : Set E} (hU : IsOpen U)
    (hcore : (F '' (({0} ×ˢ Icc (-R) R) ×ˢ {0})) ∩
      (G '' (({0} ×ˢ Icc (-S) S) ×ˢ {0})) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, r ∈ Ioo 0 ε ∧ r < R ∧ r < S ∧
      ∀ δ : ℝ, δ ≤ r →
        (F '' ((Icc (-δ) δ ×ˢ Icc (-R) R) ×ˢ Icc (-δ) δ)) ∩
          (G '' ((Icc (-δ) δ ×ˢ Icc (-S) S) ×ˢ Icc (-δ) δ)) ⊆ U := by
  let : CompactSpace (box R) :=
    isCompact_iff_compactSpace.mp ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  let : CompactSpace (box S) :=
    isCompact_iff_compactSpace.mp ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  let X : Type := (box R) × (box S)
  let B : Set X := {q | F (q.1 : (ℝ × ℝ) × ℝ) = G (q.2 : (ℝ × ℝ) × ℝ) ∧
    F (q.1 : (ℝ × ℝ) × ℝ) ∉ U}
  have hFc : Continuous (fun q : X => F (q.1 : (ℝ × ℝ) × ℝ)) :=
    hF.domRestrict.comp continuous_fst
  have hGc : Continuous (fun q : X => G (q.2 : (ℝ × ℝ) × ℝ)) :=
    hG.domRestrict.comp continuous_snd
  have hB : IsClosed B :=
    (isClosed_eq hFc hGc).inter (hU.isClosed_compl.preimage hFc)
  let w (q : X) : ℝ :=
    max ‖((q.1 : (ℝ × ℝ) × ℝ).1.1, (q.1 : (ℝ × ℝ) × ℝ).2)‖
      ‖((q.2 : (ℝ × ℝ) × ℝ).1.1, (q.2 : (ℝ × ℝ) × ℝ).2)‖
  have hw : Continuous w := by
    have hx : Continuous (fun q : X => (q.1 : (ℝ × ℝ) × ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hy : Continuous (fun q : X => (q.2 : (ℝ × ℝ) × ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact ((hx.fst.fst).prodMk hx.snd).norm.max
      (((hy.fst.fst).prodMk hy.snd).norm)
  have hwpos (q : X) (hq : q ∈ B) : 0 < w q := by
    by_contra h
    have hmax : w q ≤ 0 := le_of_not_gt h
    have hxnorm : ‖((q.1 : (ℝ × ℝ) × ℝ).1.1, (q.1 : (ℝ × ℝ) × ℝ).2)‖ = 0 :=
      le_antisymm ((le_max_left _ _).trans hmax) (norm_nonneg _)
    have hynorm : ‖((q.2 : (ℝ × ℝ) × ℝ).1.1, (q.2 : (ℝ × ℝ) × ℝ).2)‖ = 0 :=
      le_antisymm ((le_max_right _ _).trans hmax) (norm_nonneg _)
    have hxzero := norm_eq_zero.mp hxnorm
    have hyzero := norm_eq_zero.mp hynorm
    have hxcore : (q.1 : (ℝ × ℝ) × ℝ) ∈ ({0} ×ˢ Icc (-R) R) ×ˢ {0} :=
      ⟨⟨congrArg Prod.fst hxzero, q.1.property.1.2⟩, congrArg Prod.snd hxzero⟩
    have hycore : (q.2 : (ℝ × ℝ) × ℝ) ∈ ({0} ×ˢ Icc (-S) S) ×ˢ {0} :=
      ⟨⟨congrArg Prod.fst hyzero, q.2.property.1.2⟩, congrArg Prod.snd hyzero⟩
    exact hq.2 (hcore ⟨mem_image_of_mem F hxcore, ⟨q.2, hycore, hq.1.symm⟩⟩)
  obtain ⟨m, hm, hbound⟩ := hB.isCompact.exists_forall_le' hw.continuousOn hwpos
  obtain ⟨r, hr, hrsmall⟩ := exists_between (lt_min hε (lt_min hR (lt_min hS hm)))
  have hrε : r < ε := hrsmall.trans_le (min_le_left _ _)
  have hrR : r < R :=
    hrsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrS : r < S :=
    hrsmall.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hrm : r < m :=
    hrsmall.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hinterval {a b : ℝ} (hab : a ≤ b) : Icc (-a) a ⊆ Icc (-b) b := by
    intro x hx
    exact ⟨(neg_le_neg hab).trans hx.1, hx.2.trans hab⟩
  refine ⟨r, ⟨hr, hrε⟩, hrR, hrS, ?_⟩
  intro δ hδ y hy
  obtain ⟨⟨x, hx, rfl⟩, z, hz, hzx⟩ := hy
  have hxR : x ∈ box R :=
    ⟨⟨hinterval (hδ.trans hrR.le) hx.1.1, hx.1.2⟩,
      hinterval (hδ.trans hrR.le) hx.2⟩
  have hzS : z ∈ box S :=
    ⟨⟨hinterval (hδ.trans hrS.le) hz.1.1, hz.1.2⟩,
      hinterval (hδ.trans hrS.le) hz.2⟩
  let q : X := (⟨x, hxR⟩, ⟨z, hzS⟩)
  have hxnorm : ‖(x.1.1, x.2)‖ ≤ δ := by
    simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
    exact ⟨hx.1.1, hx.2⟩
  have hznorm : ‖(z.1.1, z.2)‖ ≤ δ := by
    simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
    exact ⟨hz.1.1, hz.2⟩
  have hwδ : w q ≤ δ := max_le hxnorm hznorm
  by_contra hnot
  have hm' : m ≤ w q := hbound q ⟨hzx.symm, hnot⟩
  exact (not_le_of_gt hrm) (hm'.trans (hwδ.trans hδ))

end CoordinateHalfBoxes
