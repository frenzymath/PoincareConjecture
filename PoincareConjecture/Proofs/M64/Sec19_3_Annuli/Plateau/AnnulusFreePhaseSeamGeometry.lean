import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamWeakExtension








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "v" => m64AnnulusSeamTranslation



def m64AnnulusAffineSeamExtend (u : LoopPlane → ℝ) (D : ℝ) (p : LoopPlane) : ℝ :=
  if p 0 < 0 then u (v + p) - D else u p



theorem m64AnnulusAffineSeamExtend_right (u : LoopPlane → ℝ) (D : ℝ)
    {p : LoopPlane} (hp : p ∈ S) : m64AnnulusAffineSeamExtend u D p = u p := by
  simp only [m64AnnulusAffineSeamExtend,
    not_lt.mpr ((m64AnnulusInterior_coordinates p).mp hp).1.le, ↓reduceIte]



theorem m64AnnulusAffineSeamExtend_left (u : LoopPlane → ℝ) (D : ℝ)
    {p : LoopPlane} (hp : p ∈ m64AnnulusSeamLeft) :
    m64AnnulusAffineSeamExtend u D p = u (v + p) - D := by
  simp only [m64AnnulusAffineSeamExtend,
    ((m64AnnulusSeamLeft_coordinates p).mp hp).2.1, ↓reduceIte]



theorem m64AnnulusAffineSeamExtend_sub (u : LoopPlane → ℝ) (D : ℝ)
    {p : LoopPlane} (hp : p ∈ S) : m64AnnulusAffineSeamExtend u D (p - v) = u p - D := by
  have heq : v + (p - v) = p := by abel
  have hm : p - v ∈ m64AnnulusSeamLeft := by
    change v + (p - v) ∈ S
    simpa only [heq] using hp
  rw [m64AnnulusAffineSeamExtend_left u D hm, heq]



theorem m64AnnulusAffineSeamExtend_memLp {u : LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) (D : ℝ) :
    MemLp (m64AnnulusAffineSeamExtend u D) 2 (volume.restrict O) := by
  classical
  let F := (interior m64AnnulusDomain).indicator u +
    m64AnnulusSeamLeft.indicator (fun p => u (v + p) - D)
  have hleft := (hu.sub (m64Annulus_continuous_memLp_two
    (continuous_const (y := D)))).comp_measurePreserving
      m64AnnulusSeam_translation_measurePreserving
  have hF : MemLp F 2 volume :=
    ((memLp_indicator_iff_restrict isOpen_interior.measurableSet).mpr hu).add
      ((memLp_indicator_iff_restrict m64AnnulusSeamLeft_isOpen.measurableSet).mpr hleft)
  apply (hF.mono_measure (Measure.restrict_le_self (s := O))).ae_eq
  filter_upwards [ae_restrict_of_ae m64AnnulusSeamDomain_ae_union,
    ae_restrict_mem m64AnnulusSeamDomain_isOpen.measurableSet] with p hp hO
  rcases hp.mp hO with hs | hl
  · have hnl : p ∉ m64AnnulusSeamLeft :=
      fun hl => Set.disjoint_left.mp m64AnnulusSeam_disjoint hs hl
    simp only [F, Pi.add_apply, indicator_of_mem hs, indicator_of_notMem hnl, add_zero,
      m64AnnulusAffineSeamExtend_right u D hs]
  · have hns : p ∉ S := fun hs => Set.disjoint_left.mp m64AnnulusSeam_disjoint hs hl
    simp only [F, Pi.add_apply, indicator_of_notMem hns, indicator_of_mem hl, zero_add,
      m64AnnulusAffineSeamExtend_left u D hl]



theorem m64AnnulusAffineSeam_integral_mul {u psi : LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) (D : ℝ)
    (hpsi : MemLp psi 2 (volume.restrict O)) :
    (∫ p in O, psi p * m64AnnulusAffineSeamExtend u D p) =
      (∫ p in S, (psi p + psi (p - v)) * u p) - D * ∫ p in S, psi (p - v) := by
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hr := hpsi.mono_measure (Measure.restrict_mono m64AnnulusSeam_rect_subset le_rfl)
  have hl := (hpsi.mono_measure
    (Measure.restrict_mono m64AnnulusSeam_left_subset le_rfl)).comp_measurePreserving
      m64AnnulusSeam_negative_translation_measurePreserving
  have hpair : IntegrableOn (fun p => psi p * m64AnnulusAffineSeamExtend u D p) O :=
    m64L2_test_integrable (m64AnnulusAffineSeamExtend_memLp hu D) hpsi
  have hi0 : IntegrableOn (fun p => psi p * u p) S := m64L2_test_integrable hu hr
  have hi1 : IntegrableOn (fun p => psi (p - v) * u p) S := m64L2_test_integrable hu hl
  have hiD : IntegrableOn (fun p => psi (p - v) * D) S :=
    (hl.integrable (by norm_num)).mul_const D
  rw [m64AnnulusSeam_integral _ hpair]
  have hright : (∫ p in S, psi p * m64AnnulusAffineSeamExtend u D p) =
      ∫ p in S, psi p * u p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    rw [m64AnnulusAffineSeamExtend_right u D hp]
  have hleft : (∫ p in S, psi (p - v) * m64AnnulusAffineSeamExtend u D (p - v)) =
      (∫ p in S, psi (p - v) * u p) - D * ∫ p in S, psi (p - v) := by
    calc
      _ = ∫ p in S, psi (p - v) * u p - psi (p - v) * D := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
        rw [m64AnnulusAffineSeamExtend_sub u D hp, mul_sub]
      _ = _ := by rw [integral_sub hi1 hiD, integral_mul_const, mul_comm D]
  rw [hright, hleft]
  simp_rw [add_mul]
  rw [integral_add hi0 hi1]
  ring

end PoincareConjecture
