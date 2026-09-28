import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetResidual










noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem actual_comp_derivative_memLp
    {q : ℂ → E} {H : E → F} {K U : Set ℂ} {V : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V)
    (hq : ContinuousOn q K) (hq1 : ContDiffOn ℝ 1 q U)
    (hqV : MapsTo q K V) (hH : ContDiffOn ℝ 1 H V)
    (v : ℂ) (hdq : MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict (K ∩ U))) :
    MemLp (fun z => fderiv ℝ (H ∘ q) z v) 2 (volume.restrict (K ∩ U)) := by
  have hD : ContinuousOn (fderiv ℝ H) V := hH.continuousOn_fderiv_of_isOpen hV (by simp)
  have hDq : ContinuousOn (fun z => fderiv ℝ H (q z)) K := hD.comp hq hqV
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hDq
  have hKU : MeasurableSet (K ∩ U) := hK.measurableSet.inter hU.measurableSet
  have hm : AEStronglyMeasurable (fun z => fderiv ℝ H (q z))
      (volume.restrict (K ∩ U)) :=
    (hDq.mono inter_subset_left).aestronglyMeasurable hKU
  have hh : MemLp (fun z => fderiv ℝ H (q z) (fderiv ℝ q z v))
      2 (volume.restrict (K ∩ U)) := by
    apply hdq.of_le_mul (c := C)
    · exact (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).aestronglyMeasurable_comp₂ hm hdq.1
    · filter_upwards [ae_restrict_mem hKU] with z hz
      exact ((fderiv ℝ H (q z)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hC z hz.1) (norm_nonneg _))
  apply hh.ae_eq
  filter_upwards [ae_restrict_mem hKU] with z hz
  have hdz := ((hH.contDiffAt (hV.mem_nhds (hqV hz.1))).differentiableAt
    one_ne_zero).hasFDerivAt.comp z
      ((hq1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero).hasFDerivAt
  exact (congrArg (fun L : ℂ →L[ℝ] F => L v) hdz.fderiv).symm




def twoPlaneProjection (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) : E →L[ℝ] E :=
  (G a a)⁻¹ • ((G a).smulRight a + (G b).smulRight b)



theorem twoPlaneProjection_apply (G : E →L[ℝ] E →L[ℝ] ℝ) (a b v : E) :
    twoPlaneProjection G a b v = (G a a)⁻¹ • (G a v • a + G b v • b) := rfl



theorem twoPlaneProjection_fixes (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ v w, G v w = G w v) {a b : E}
    (hpos : G a a ≠ 0) (hab : G a b = 0) (hbb : G b b = G a a) :
    twoPlaneProjection G a b a = a ∧ twoPlaneProjection G a b b = b := by
  have hba : G b a = 0 := (hG b a).trans hab
  constructor
  · rw [twoPlaneProjection_apply, hba, zero_smul, add_zero, smul_smul,
      inv_mul_cancel₀ hpos, one_smul]
  · rw [twoPlaneProjection_apply, hab, zero_smul, zero_add, hbb, smul_smul,
      inv_mul_cancel₀ hpos, one_smul]



theorem twoPlaneProjection_normal (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ v w, G v w = G w v) {a b : E}
    (hpos : G a a ≠ 0) (hab : G a b = 0) (hbb : G b b = G a a) (v : E) :
    G (v - twoPlaneProjection G a b v) a = 0 ∧
      G (v - twoPlaneProjection G a b v) b = 0 := by
  have hba : G b a = 0 := (hG b a).trans hab
  rw [twoPlaneProjection_apply]
  simp only [map_sub, sub_apply, map_smul, smul_apply, map_add, add_apply, smul_eq_mul]
  rw [hba, hab, hbb, hG v a, hG v b]
  constructor <;> field_simp <;> ring



theorem twoPlaneProjection_idempotent (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ v w, G v w = G w v) {a b : E}
    (hpos : G a a ≠ 0) (hab : G a b = 0) (hbb : G b b = G a a) (v : E) :
    twoPlaneProjection G a b (twoPlaneProjection G a b v) =
      twoPlaneProjection G a b v := by
  have hfix := twoPlaneProjection_fixes G hG hpos hab hbb
  nth_rw 2 [twoPlaneProjection_apply]
  rw [map_smul, map_add, map_smul, map_smul, hfix.1, hfix.2]
  rfl




theorem contDiffOn_twoPlaneProjection :
    ContDiffOn ℝ ∞
      (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E × E) => twoPlaneProjection q.1 q.2.1 q.2.2)
      {q | q.1 q.2.1 q.2.1 ≠ 0} := by
  have ha : ContDiff ℝ ∞ (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E × E) => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hb : ContDiff ℝ ∞ (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E × E) => q.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hGa := contDiff_fst.clm_apply ha
  have hGb := contDiff_fst.clm_apply hb
  exact ((hGa.clm_apply ha).contDiffOn.inv (fun _ h => h)).smul
    ((hGa.smulRight ha).add (hGb.smulRight hb)).contDiffOn





theorem twoPlaneProjection_rotate_scale (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ v w, G v w = G w v) {a b : E}
    (hab : G a b = 0) (hbb : G b b = G a a)
    (c d : ℝ) (hcd : c ^ 2 + d ^ 2 ≠ 0) :
    twoPlaneProjection G (c • a + d • b) ((-d) • a + c • b) =
      twoPlaneProjection G a b := by
  have hba : G b a = 0 := (hG b a).trans hab
  have hden : G (c • a + d • b) (c • a + d • b) =
      (c ^ 2 + d ^ 2) * G a a := by
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hab, hba, hbb]
    ring
  apply ContinuousLinearMap.ext
  intro v
  have hnum : G (c • a + d • b) v • (c • a + d • b) +
      G ((-d) • a + c • b) v • ((-d) • a + c • b) =
      (c ^ 2 + d ^ 2) • (G a v • a + G b v • b) := by
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    module
  rw [twoPlaneProjection_apply, hden, hnum, twoPlaneProjection_apply, smul_smul,
    mul_inv_rev, mul_assoc, inv_mul_cancel₀ hcd, mul_one]




theorem normal_second_derivative_eq_projection_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {P : X → E →L[ℝ] E} {f : X → E} {z : X}
    (hP : DifferentiableAt ℝ P z) (hf : ContDiffAt ℝ 2 f z)
    (v w : X)
    (hfix : ∀ᶠ y in 𝓝 z, P y (fderiv ℝ f y w) = fderiv ℝ f y w) :
    fderiv ℝ (fderiv ℝ f) z v w - P z (fderiv ℝ (fderiv ℝ f) z v w) =
      fderiv ℝ P z v (fderiv ℝ f z w) := by
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt one_ne_zero
  have hcol := hDf.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  have hprod := hP.hasFDerivAt.clm_apply hcol
  have he : (fun y => P y (fderiv ℝ f y w)) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ f y w) := hfix
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [hprod.fderiv, hcol.fderiv] at hd
  have hv := congrArg (fun L : X →L[ℝ] E => L v) hd
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, zero_add, map_zero] at hv
  exact (eq_sub_of_add_eq' hv).symm






theorem twoPlaneProjection_derivative_memLp
    {G : ℂ → E →L[ℝ] E →L[ℝ] ℝ} {a b : ℂ → E} {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U)
    (hG : ContinuousOn G K) (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hG1 : ContDiffOn ℝ 1 G U) (ha1 : ContDiffOn ℝ 1 a U)
    (hb1 : ContDiffOn ℝ 1 b U)
    (hne : ∀ z ∈ K, G z (a z) (a z) ≠ 0) (v : ℂ)
    (hDG : MemLp (fun z => fderiv ℝ G z v) 2 (volume.restrict (K ∩ U)))
    (hDa : MemLp (fun z => fderiv ℝ a z v) 2 (volume.restrict (K ∩ U)))
    (hDb : MemLp (fun z => fderiv ℝ b z v) 2 (volume.restrict (K ∩ U))) :
    MemLp (fun z => fderiv ℝ (fun w => twoPlaneProjection (G w) (a w) (b w)) z v)
      2 (volume.restrict (K ∩ U)) := by
  let : NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] ℝ) × (E × E)) := inferInstance
  let : NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] ℝ) × (E × E)) := inferInstance
  let q : ℂ → (E →L[ℝ] E →L[ℝ] ℝ) × (E × E) := fun z => (G z, a z, b z)
  let V : Set ((E →L[ℝ] E →L[ℝ] ℝ) × (E × E)) := {w | w.1 w.2.1 w.2.1 ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun
    ((continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply
      (continuous_fst.comp continuous_snd)) continuous_const
  have hq : ContinuousOn q K := hG.prodMk (ha.prodMk hb)
  have hq1 : ContDiffOn ℝ 1 q U := hG1.prodMk (ha1.prodMk hb1)
  have hdq : MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict (K ∩ U)) := by
    have hh : MemLp (fun z => (fderiv ℝ G z v, fderiv ℝ a z v, fderiv ℝ b z v))
        2 (volume.restrict (K ∩ U)) :=
      memLp_prod_iff.mpr ⟨hDG, memLp_prod_iff.mpr ⟨hDa, hDb⟩⟩
    apply hh.ae_eq
    filter_upwards [ae_restrict_mem (hK.measurableSet.inter hU.measurableSet)] with z hz
    have hD := ((hG1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt
      one_ne_zero).hasFDerivAt.prodMk
        (((ha1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero).hasFDerivAt.prodMk
          ((hb1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero).hasFDerivAt)
    exact (congrArg (fun L : ℂ →L[ℝ] ((E →L[ℝ] E →L[ℝ] ℝ) × (E × E)) => L v)
      hD.fderiv).symm
  have hqV : MapsTo q K V := fun z hz => hne z hz
  exact actual_comp_derivative_memLp hK hU hV hq hq1 hqV
    (contDiffOn_twoPlaneProjection.of_le (by simp)) v hdq

end PoincareConjecture.M65Branch
