import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "v" => m64AnnulusRadialTranslation




theorem m64AnnulusLowerExtend_memLp
    {E : Type*} [NormedAddCommGroup E] {q : ENNReal} {f g : LoopPlane → E}
    (hf : MemLp f q (volume.restrict S)) (hg : MemLp g q (volume.restrict S)) :
    MemLp (m64AnnulusLowerExtend f g) q (volume.restrict O) := by
  classical
  let F := (interior m64AnnulusDomain).indicator g +
    m64AnnulusLowerStrip.indicator (fun p => f (v + p))
  have hbottom : MemLp (fun p => f (v + p)) q (volume.restrict m64AnnulusLowerStrip) := by
    simpa only [Function.comp_def] using
      hf.comp_measurePreserving m64AnnulusLower_translation_measurePreserving
  have hF : MemLp F q volume :=
    ((memLp_indicator_iff_restrict isOpen_interior.measurableSet).mpr hg).add
      ((memLp_indicator_iff_restrict m64AnnulusLowerStrip_isOpen.measurableSet).mpr hbottom)
  apply (hF.mono_measure (Measure.restrict_le_self (s := O))).ae_eq
  filter_upwards [ae_restrict_of_ae m64AnnulusLowerDomain_ae_union,
    ae_restrict_mem m64AnnulusLowerDomain_isOpen.measurableSet] with p hp hpO
  have hU : p ∈ S ∪ m64AnnulusLowerStrip := hp.mp hpO
  rcases hU with hs | hl
  · have hnl : p ∉ m64AnnulusLowerStrip :=
      fun hl => disjoint_left.mp m64AnnulusLower_disjoint hs hl
    simp only [F, Pi.add_apply, indicator_of_mem hs, indicator_of_notMem hnl, add_zero,
      m64AnnulusLowerExtend_right f g hs]
  · have hns : p ∉ S := fun hs => disjoint_left.mp m64AnnulusLower_disjoint hs hl
    simp only [F, Pi.add_apply, indicator_of_notMem hns, indicator_of_mem hl, zero_add,
      m64AnnulusLowerExtend_left f g hl]




theorem m64AnnulusLower_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : LoopPlane → E) (hF : IntegrableOn F O volume) :
    (∫ p in O, F p) = (∫ p in S, F p) + ∫ p in S, F (p - v) := by
  rw [setIntegral_congr_set m64AnnulusLowerDomain_ae_union,
    setIntegral_union m64AnnulusLower_disjoint m64AnnulusLowerStrip_isOpen.measurableSet
      (hF.mono_set m64AnnulusLower_rect_subset) (hF.mono_set m64AnnulusLower_strip_subset)]
  congr 1
  exact (m64AnnulusLower_negative_translation_measurePreserving.integral_comp
    (by
      have hfun : (fun p : LoopPlane => p - v) = fun p => -v + p := by
        funext p
        abel
      rw [hfun]
      exact (MeasurableEquiv.addLeft (-v)).measurableEmbedding) F).symm




theorem m64AnnulusLowerExtend_integral_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : LoopPlane → E} {phi : LoopPlane → ℝ}
    (hf : MemLp f 2 (volume.restrict S)) (hg : MemLp g 2 (volume.restrict S))
    (hp : MemLp phi 2 (volume.restrict O)) :
    (∫ p in O, phi p • m64AnnulusLowerExtend f g p) =
      (∫ p in S, phi p • g p) + ∫ p in S, phi (p - v) • f p := by
  rw [m64AnnulusLower_integral _
    (m64L2_test_integrable (m64AnnulusLowerExtend_memLp hf hg) hp)]
  congr 1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hpS
    rw [m64AnnulusLowerExtend_right f g hpS]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hpS
    rw [m64AnnulusLowerExtend_sub f g hpS]

end PoincareConjecture
