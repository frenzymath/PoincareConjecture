import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamTests
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.CutBoundary
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "v" => m64AnnulusSeamTranslation

theorem m64AnnulusInterior_coordinates (p : LoopPlane) :
    p ∈ S ↔ 0 < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1 := by
  let h : LoopPlane ≃ₜ ℝ × ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans (Homeomorph.finTwoArrow (X := ℝ))
  have hdom : m64AnnulusDomain = h ⁻¹' (Icc (0 : ℝ) curvePeriod ×ˢ Icc (0 : ℝ) 1) := by
    ext q
    change (0 ≤ q 0 ∧ q 0 ≤ curvePeriod ∧ 0 ≤ q 1 ∧ q 1 ≤ 1) ↔
      (0 ≤ q 0 ∧ q 0 ≤ curvePeriod) ∧ (0 ≤ q 1 ∧ q 1 ≤ 1)
    tauto
  rw [hdom, ← h.preimage_interior, interior_prod_eq, interior_Icc, interior_Icc]
  change ((0 < p 0 ∧ p 0 < curvePeriod) ∧ (0 < p 1 ∧ p 1 < 1)) ↔ _
  tauto

def m64AnnulusSeamLeft : Set LoopPlane := (fun p => v + p) ⁻¹' S

theorem m64AnnulusSeamLeft_isOpen : IsOpen m64AnnulusSeamLeft :=
  isOpen_interior.preimage (continuous_const.add continuous_id)

theorem m64AnnulusSeamLeft_coordinates (p : LoopPlane) :
    p ∈ m64AnnulusSeamLeft ↔
      -curvePeriod < p 0 ∧ p 0 < 0 ∧ 0 < p 1 ∧ p 1 < 1 := by
  change v + p ∈ S ↔ _
  rw [m64AnnulusInterior_coordinates]
  simp only [m64AnnulusSeamTranslation, annulusPoint, PiLp.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
  constructor <;> intro h <;> constructor <;> try linarith [h.1, h.2.1]
  · exact ⟨by linarith [h.2.1], h.2.2⟩
  · exact ⟨by linarith [h.2.1], h.2.2⟩

theorem m64AnnulusSeam_rect_subset : S ⊆ m64AnnulusSeamDomain := by
  intro p hp
  have h := (m64AnnulusInterior_coordinates p).mp hp
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  exact ⟨by linarith [h.1], h.2⟩

theorem m64AnnulusSeam_left_subset : m64AnnulusSeamLeft ⊆ m64AnnulusSeamDomain := by
  intro p hp
  have h := (m64AnnulusSeamLeft_coordinates p).mp hp
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  exact ⟨h.1, by linarith [h.2.1], h.2.2⟩

theorem m64AnnulusSeam_disjoint : Disjoint S m64AnnulusSeamLeft := by
  apply disjoint_left.mpr
  intro p hp hq
  exact (lt_asymm ((m64AnnulusInterior_coordinates p).mp hp).1
    ((m64AnnulusSeamLeft_coordinates p).mp hq).2.1)

theorem m64AnnulusSeamDomain_ae_union :
    m64AnnulusSeamDomain =ᵐ[volume] (S ∪ m64AnnulusSeamLeft : Set LoopPlane) := by
  have hzero : ∀ᵐ p : LoopPlane ∂volume, p 0 ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_cut_line_null 0
  filter_upwards [hzero] with p hp
  apply propext
  constructor
  · intro h
    rcases lt_or_gt_of_ne hp with hl | hr
    · exact Or.inr ((m64AnnulusSeamLeft_coordinates p).mpr ⟨h.1, hl, h.2.2⟩)
    · exact Or.inl ((m64AnnulusInterior_coordinates p).mpr ⟨hr, h.2⟩)
  · rintro (h | h)
    · exact m64AnnulusSeam_rect_subset h
    · exact m64AnnulusSeam_left_subset h

theorem m64AnnulusSeam_translation_measurePreserving :
    MeasurePreserving (fun p : LoopPlane => v + p)
      (volume.restrict m64AnnulusSeamLeft) (volume.restrict S) :=
  (measurePreserving_add_left (volume : Measure LoopPlane) v).restrict_preimage_emb
    (MeasurableEquiv.addLeft v).measurableEmbedding S

theorem m64AnnulusSeam_negative_translation_measurePreserving :
    MeasurePreserving (fun p : LoopPlane => p - v)
      (volume.restrict S) (volume.restrict m64AnnulusSeamLeft) := by
  have h := (measurePreserving_add_left (volume : Measure LoopPlane) (-v)).restrict_preimage_emb
    (MeasurableEquiv.addLeft (-v)).measurableEmbedding m64AnnulusSeamLeft
  have hpre : (fun p : LoopPlane => -v + p) ⁻¹' m64AnnulusSeamLeft = S := by
    ext p
    simp only [m64AnnulusSeamLeft, mem_preimage, add_neg_cancel_left]
  rw [hpre] at h
  convert h using 1
  funext p
  abel

def m64AnnulusSeamExtend {E : Type*} (f : LoopPlane → E) (p : LoopPlane) : E :=
  if p 0 < 0 then f (v + p) else f p

theorem m64AnnulusSeamExtend_right {E : Type*} (f : LoopPlane → E)
    {p : LoopPlane} (hp : p ∈ S) : m64AnnulusSeamExtend f p = f p := by
  simp only [m64AnnulusSeamExtend, not_lt.mpr ((m64AnnulusInterior_coordinates p).mp hp).1.le,
    ↓reduceIte]

theorem m64AnnulusSeamExtend_left {E : Type*} (f : LoopPlane → E)
    {p : LoopPlane} (hp : p ∈ m64AnnulusSeamLeft) :
    m64AnnulusSeamExtend f p = f (v + p) := by
  simp only [m64AnnulusSeamExtend, ((m64AnnulusSeamLeft_coordinates p).mp hp).2.1, ↓reduceIte]

theorem m64AnnulusSeamExtend_comp {E F : Type*} (f : LoopPlane → E) (g : E → F) :
    g ∘ m64AnnulusSeamExtend f = m64AnnulusSeamExtend (g ∘ f) := by
  funext p
  simp only [Function.comp_def, m64AnnulusSeamExtend]
  split_ifs <;> rfl

theorem m64AnnulusSeamExtend_sub {E : Type*} (f : LoopPlane → E)
    {p : LoopPlane} (hp : p ∈ S) : m64AnnulusSeamExtend f (p - v) = f p := by
  have heq : v + (p - v) = p := by abel
  have hm : p - v ∈ m64AnnulusSeamLeft := by
    change v + (p - v) ∈ S
    simpa only [heq] using hp
  rw [m64AnnulusSeamExtend_left f hm, heq]

theorem m64AnnulusSeamExtend_memLp {E : Type*} [NormedAddCommGroup E]
    {q : ENNReal} {f : LoopPlane → E} (hf : MemLp f q (volume.restrict S)) :
    MemLp (m64AnnulusSeamExtend f) q (volume.restrict m64AnnulusSeamDomain) := by
  classical
  let F := (interior m64AnnulusDomain).indicator f +
    m64AnnulusSeamLeft.indicator (fun p => f (v + p))
  have hleft := hf.comp_measurePreserving m64AnnulusSeam_translation_measurePreserving
  have hF : MemLp F q volume :=
    ((memLp_indicator_iff_restrict isOpen_interior.measurableSet).mpr hf).add
      ((memLp_indicator_iff_restrict m64AnnulusSeamLeft_isOpen.measurableSet).mpr hleft)
  apply (hF.mono_measure (Measure.restrict_le_self (s := m64AnnulusSeamDomain))).ae_eq
  filter_upwards [ae_restrict_of_ae m64AnnulusSeamDomain_ae_union,
    ae_restrict_mem m64AnnulusSeamDomain_isOpen.measurableSet] with p hp hO
  have hU : p ∈ S ∪ m64AnnulusSeamLeft := hp.mp hO
  rcases hU with hs | hl
  · have hnl : p ∉ m64AnnulusSeamLeft :=
      fun hl => Set.disjoint_left.mp m64AnnulusSeam_disjoint hs hl
    simp only [F, Pi.add_apply, indicator_of_mem hs, indicator_of_notMem hnl, add_zero,
      m64AnnulusSeamExtend_right f hs]
  · have hns : p ∉ S := fun hs => Set.disjoint_left.mp m64AnnulusSeam_disjoint hs hl
    simp only [F, Pi.add_apply, indicator_of_notMem hns, indicator_of_mem hl, zero_add,
      m64AnnulusSeamExtend_left f hl]

theorem m64AnnulusSeam_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : LoopPlane → E) (hF : IntegrableOn F m64AnnulusSeamDomain volume) :
    (∫ p in m64AnnulusSeamDomain, F p) =
      (∫ p in S, F p) + ∫ p in S, F (p - v) := by
  rw [setIntegral_congr_set m64AnnulusSeamDomain_ae_union,
    setIntegral_union m64AnnulusSeam_disjoint m64AnnulusSeamLeft_isOpen.measurableSet
      (hF.mono_set m64AnnulusSeam_rect_subset) (hF.mono_set m64AnnulusSeam_left_subset)]
  congr 1
  exact (m64AnnulusSeam_negative_translation_measurePreserving.integral_comp
    (by
      have hfun : (fun p : LoopPlane => p - v) = fun p => -v + p := by
        funext p
        abel
      rw [hfun]
      exact (MeasurableEquiv.addLeft (-v)).measurableEmbedding) F).symm

theorem m64AnnulusSeamExtend_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : LoopPlane → E) (hf : IntegrableOn f S volume) :
    (∫ p in m64AnnulusSeamDomain, m64AnnulusSeamExtend f p) = 2 • ∫ p in S, f p := by
  have hfe : IntegrableOn (m64AnnulusSeamExtend f) m64AnnulusSeamDomain volume :=
    memLp_one_iff_integrable.mp (m64AnnulusSeamExtend_memLp (memLp_one_iff_integrable.mpr hf))
  rw [m64AnnulusSeam_integral _ hfe]
  have hr : (∫ p in S, m64AnnulusSeamExtend f p) = ∫ p in S, f p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact m64AnnulusSeamExtend_right f hp
  have hl : (∫ p in S, m64AnnulusSeamExtend f (p - v)) = ∫ p in S, f p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact m64AnnulusSeamExtend_sub f hp
  rw [hr, hl, two_smul]

end PoincareConjecture
