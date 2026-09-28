import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamPatch

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "v" => m64AnnulusSeamTranslation

theorem m64AnnulusSeamPatch_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKO : K ⊆ O)
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    {f g : LoopPlane → E} (hf : IntegrableOn f K volume) (hg : IntegrableOn g S volume) :
    (∫ p in S, m64AnnulusSeamPatch K f g p) =
      (∫ p in S, g p) + ∫ p in K, f p - m64AnnulusSeamExtend g p := by
  let d := K.indicator (f - m64AnnulusSeamExtend g)
  have hfM : MemLp f 1 (volume.restrict K) := memLp_one_iff_integrable.mpr hf
  have hgM : MemLp g 1 (volume.restrict S) := memLp_one_iff_integrable.mpr hg
  have hdM : MemLp d 1 volume := (memLp_indicator_iff_restrict hK).mpr
    (hfM.sub ((m64AnnulusSeamExtend_memLp hgM).mono_measure (Measure.restrict_mono hKO le_rfl)))
  have hdshift : MemLp (fun p => d (p - v)) 1 volume := by
    have h := hdM.comp_measurePreserving
      (measurePreserving_add_right (volume : Measure LoopPlane) (-v))
    simpa only [sub_eq_add_neg, Function.comp_def] using h
  have hd : IntegrableOn d S volume :=
    memLp_one_iff_integrable.mp (hdM.mono_measure Measure.restrict_le_self)
  have hshift : IntegrableOn (fun p => d (p - v)) S volume :=
    memLp_one_iff_integrable.mp (hdshift.mono_measure Measure.restrict_le_self)
  have hgd : IntegrableOn (fun p => g p + d p) S volume := hg.add hd
  have hcorr := m64AnnulusSeam_integral d
    (memLp_one_iff_integrable.mp (hdM.mono_measure Measure.restrict_le_self))
  have hcorrK : (∫ p in O, d p) = ∫ p in K, f p - m64AnnulusSeamExtend g p := by
    rw [show d = K.indicator (f - m64AnnulusSeamExtend g) from rfl,
      setIntegral_indicator hK, inter_eq_right.mpr hKO]
    rfl
  calc
    _ = ∫ p in S, (g p + d p) + d (p - v) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
      exact m64AnnulusSeamPatch_eq_add hsep f g hp
    _ = ((∫ p in S, g p) + ∫ p in S, d p) + ∫ p in S, d (p - v) := by
      rw [integral_add hgd hshift, integral_add hg hd]
    _ = (∫ p in S, g p) + ∫ p in O, d p := by rw [hcorr]; abel
    _ = _ := by rw [hcorrK]

theorem m64AnnulusSeamExtend_smul {E : Type*} [SMul ℝ E]
    (phi : LoopPlane → ℝ) (f : LoopPlane → E) (p : LoopPlane) :
    m64AnnulusSeamExtend (fun q => phi q • f q) p =
      m64AnnulusSeamExtend phi p • m64AnnulusSeamExtend f p := by
  simp only [m64AnnulusSeamExtend]
  split_ifs <;> rfl

theorem m64AnnulusSeamPatch_smul_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKO : K ⊆ O)
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    {f g : LoopPlane → E} {phi : LoopPlane → ℝ}
    (hf : MemLp f 2 (volume.restrict K)) (hg : MemLp g 2 (volume.restrict S))
    (hphi : MemLp phi 2 (volume.restrict S)) :
    (∫ p in S, phi p • m64AnnulusSeamPatch K f g p) =
      (∫ p in S, phi p • g p) +
        ∫ p in K, m64AnnulusSeamExtend phi p • (f p - m64AnnulusSeamExtend g p) := by
  classical
  have hpK := (m64AnnulusSeamExtend_memLp hphi).mono_measure (Measure.restrict_mono hKO le_rfl)
  have h := m64AnnulusSeamPatch_integral hK hKO hsep
    (m64L2_test_integrable hf hpK) (m64L2_test_integrable hg hphi)
  have heq : (∫ p in S, phi p • m64AnnulusSeamPatch K f g p) =
      ∫ p in S, m64AnnulusSeamPatch K (fun q => m64AnnulusSeamExtend phi q • f q)
        (fun q => phi q • g q) p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    by_cases hpK : p ∈ K
    · simp only [m64AnnulusSeamPatch, if_pos hpK, m64AnnulusSeamExtend_right phi hp]
    · by_cases hqK : p - v ∈ K
      · simp only [m64AnnulusSeamPatch, if_neg hpK, if_pos hqK, m64AnnulusSeamExtend_sub phi hp]
      · simp only [m64AnnulusSeamPatch, if_neg hpK, if_neg hqK]
  rw [heq, h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  rw [m64AnnulusSeamExtend_smul, smul_sub]

theorem m64AnnulusSeamPatch_flux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKO : K ⊆ O)
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    (u0 u1 W0 W1 : LoopPlane → E) (phi psi : LoopPlane → ℝ)
    (hu0 : MemLp u0 2 (volume.restrict S)) (hu1 : MemLp u1 2 (volume.restrict K))
    (hW0 : MemLp W0 2 (volume.restrict S)) (hW1 : MemLp W1 2 (volume.restrict K))
    (hp : MemLp phi 2 (volume.restrict S)) (hq : MemLp psi 2 (volume.restrict S))
    (hgreen :
      (∫ p in K, m64AnnulusSeamExtend phi p • W1 p) +
        (∫ p in K, m64AnnulusSeamExtend psi p • u1 p) =
      (∫ p in K, m64AnnulusSeamExtend phi p • m64AnnulusSeamExtend W0 p) +
        (∫ p in K, m64AnnulusSeamExtend psi p • m64AnnulusSeamExtend u0 p)) :
    (∫ p in S, phi p • m64AnnulusSeamPatch K W1 W0 p) +
      (∫ p in S, psi p • m64AnnulusSeamPatch K u1 u0 p) =
    (∫ p in S, phi p • W0 p) + (∫ p in S, psi p • u0 p) := by
  have hpK := (m64AnnulusSeamExtend_memLp hp).mono_measure (Measure.restrict_mono hKO le_rfl)
  have hqK := (m64AnnulusSeamExtend_memLp hq).mono_measure (Measure.restrict_mono hKO le_rfl)
  have huK := (m64AnnulusSeamExtend_memLp hu0).mono_measure (Measure.restrict_mono hKO le_rfl)
  have hWK := (m64AnnulusSeamExtend_memLp hW0).mono_measure (Measure.restrict_mono hKO le_rfl)
  rw [m64AnnulusSeamPatch_smul_integral hK hKO hsep hW1 hW0 hp,
    m64AnnulusSeamPatch_smul_integral hK hKO hsep hu1 hu0 hq]
  simp only [smul_sub]
  rw [integral_sub (m64L2_test_integrable hW1 hpK) (m64L2_test_integrable hWK hpK),
    integral_sub (m64L2_test_integrable hu1 hqK) (m64L2_test_integrable huK hqK)]
  calc
    _ = ((∫ p in S, phi p • W0 p) + ∫ p in S, psi p • u0 p) +
        (((∫ p in K, m64AnnulusSeamExtend phi p • W1 p) +
          ∫ p in K, m64AnnulusSeamExtend psi p • u1 p) -
        ((∫ p in K, m64AnnulusSeamExtend phi p • m64AnnulusSeamExtend W0 p) +
          ∫ p in K, m64AnnulusSeamExtend psi p • m64AnnulusSeamExtend u0 p)) := by abel
    _ = _ := by rw [hgreen, sub_self, add_zero]

end PoincareConjecture
