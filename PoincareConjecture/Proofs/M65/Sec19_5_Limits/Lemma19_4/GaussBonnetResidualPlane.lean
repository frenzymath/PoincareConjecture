import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetProjection
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchComplexGradient










noncomputable section

set_option autoImplicit false

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {n : ℕ}



def residualRealColumn : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun q => WithLp.toLp 2 (fun i => (q i).re)
    map_add' := by intro v w; ext i; exact add_re _ _
    map_smul' := by intro r v; ext i; exact smul_re _ _ }




def residualImagColumn : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun q => WithLp.toLp 2 (fun i => -(q i).im)
    map_add' := by
      intro v w
      ext i
      change -(v i + w i).im = -(v i).im + -(w i).im
      rw [add_im, neg_add]
    map_smul' := by
      intro r v
      ext i
      change -(r • v i).im = r * -(v i).im
      rw [smul_im, smul_eq_mul, mul_neg] }



theorem residual_columns_recover (q : Fin n → ℂ) :
    coordinateComplexification (residualRealColumn q) -
      I • coordinateComplexification (residualImagColumn q) = q := by
  ext i
  change ((q i).re : ℂ) - I * (-(q i).im : ℝ) = q i
  rw [ofReal_neg, mul_neg, sub_neg_eq_add]
  simpa only [mul_comm] using Complex.re_add_im (q i)




theorem residual_columns_complexGradient (H : ℂ → EuclideanSpace ℝ (Fin n)) (z : ℂ) :
    residualRealColumn (complexGradient H z) = fderiv ℝ H z 1 ∧
      residualImagColumn (complexGradient H z) = fderiv ℝ H z I := by
  constructor <;> ext i
  · change (((fderiv ℝ H z 1 i : ℝ) : ℂ) - I * ((fderiv ℝ H z I i : ℝ) : ℂ)).re = _
    simp
  · change -(((fderiv ℝ H z 1 i : ℝ) : ℂ) - I * ((fderiv ℝ H z I i : ℝ) : ℂ)).im = _
    simp




theorem residual_columns_smul (s : ℂ) (q : Fin n → ℂ) :
    residualRealColumn (s • q) = s.re • residualRealColumn q + s.im • residualImagColumn q ∧
      residualImagColumn (s • q) =
        (-s.im) • residualRealColumn q + s.re • residualImagColumn q := by
  constructor <;> ext i
  · change (s * q i).re = s.re * (q i).re + s.im * -(q i).im
    rw [mul_re]
    ring
  · change -(s * q i).im = -s.im * (q i).re + s.re * -(q i).im
    rw [mul_im]
    ring




theorem conformal_columns_rotate_scale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (hG : ∀ v w, G v w = G w v)
    {a b : E} (hab : G a b = 0) (hbb : G b b = G a a) (c d : ℝ) :
    G (c • a + d • b) ((-d) • a + c • b) = 0 ∧
      G ((-d) • a + c • b) ((-d) • a + c • b) =
        G (c • a + d • b) (c • a + d • b) := by
  have hba : G b a = 0 := (hG b a).trans hab
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hab, hba, hbb]
  constructor <;> ring




theorem residual_columns_conformal_of_smul
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hG : ∀ v w, G v w = G w v) {s : ℂ} (hs : s ≠ 0) (q : Fin n → ℂ)
    (hcross : G (residualRealColumn (s • q)) (residualImagColumn (s • q)) = 0)
    (hdiag : G (residualImagColumn (s • q)) (residualImagColumn (s • q)) =
      G (residualRealColumn (s • q)) (residualRealColumn (s • q))) :
    G (residualRealColumn q) (residualImagColumn q) = 0 ∧
      G (residualImagColumn q) (residualImagColumn q) =
        G (residualRealColumn q) (residualRealColumn q) := by
  have hrot := conformal_columns_rotate_scale G hG hcross hdiag s⁻¹.re s⁻¹.im
  obtain ⟨ha, hb⟩ := residual_columns_smul s⁻¹ (s • q)
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at ha hb
  simpa only [← ha, ← hb] using hrot




theorem residual_columns_factor_pos
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hpos : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < G v v)
    {q : Fin n → ℂ} (hq : q ≠ 0)
    (hdiag : G (residualImagColumn q) (residualImagColumn q) =
      G (residualRealColumn q) (residualRealColumn q)) :
    0 < G (residualRealColumn q) (residualRealColumn q) := by
  apply hpos
  intro hr
  have hi : residualImagColumn q = 0 := by
    by_contra hi
    have hpositive := hpos (residualImagColumn q) hi
    rw [hdiag, hr, map_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  apply hq
  rw [← residual_columns_recover q, hr, hi, map_zero, smul_zero, sub_zero]




theorem residual_projection_eq_of_gradient_factor
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hG : ∀ v w, G v w = G w v)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {z s : ℂ} {q : Fin n → ℂ}
    (hs : s ≠ 0) (hfactor : complexGradient H z = s • q)
    (hcross : G (fderiv ℝ H z 1) (fderiv ℝ H z I) = 0)
    (hdiag : G (fderiv ℝ H z I) (fderiv ℝ H z I) =
      G (fderiv ℝ H z 1) (fderiv ℝ H z 1)) :
    twoPlaneProjection G (residualRealColumn q) (residualImagColumn q) =
      twoPlaneProjection G (fderiv ℝ H z 1) (fderiv ℝ H z I) := by
  obtain ⟨ha, hb⟩ := residual_columns_complexGradient H z
  rw [hfactor] at ha hb
  obtain ⟨hc, hd⟩ := residual_columns_conformal_of_smul G hG hs q
    (by simpa only [ha, hb] using hcross) (by simpa only [ha, hb] using hdiag)
  obtain ⟨hsa, hsb⟩ := residual_columns_smul s q
  have hnorm : s.re ^ 2 + s.im ^ 2 ≠ 0 := by
    simpa only [Complex.normSq_apply, sq] using mt Complex.normSq_eq_zero.mp hs
  rw [← ha, ← hb, hsa, hsb]
  exact (twoPlaneProjection_rotate_scale G hG hc hd s.re s.im hnorm).symm





theorem residual_projection_extension_memLp
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {q : ℂ → Fin n → ℂ}
    {G : ℂ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hUK : U ⊆ K) (hKU : K ⊆ closure U)
    (hG : ContinuousOn G K) (hG1 : ContDiffOn ℝ 1 G U)
    (hGsymm : ∀ z ∈ K, ∀ v w, G z v w = G z w v)
    (hGpos : ∀ z ∈ K, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < G z v v)
    (hq : ContinuousOn q K) (hq1 : ContDiffOn ℝ 1 q U)
    (hqne : ∀ z ∈ K, q z ≠ 0)
    (hfactor : ∀ z ∈ U, ∃ s : ℂ, s ≠ 0 ∧ complexGradient H z = s • q z)
    (hconf : ∀ z ∈ U,
      G z (fderiv ℝ H z 1) (fderiv ℝ H z I) = 0 ∧
        G z (fderiv ℝ H z I) (fderiv ℝ H z I) = G z (fderiv ℝ H z 1) (fderiv ℝ H z 1))
    (v : ℂ)
    (hdG : MemLp (fun z => fderiv ℝ G z v) 2 (volume.restrict (K ∩ U)))
    (hdq : MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict (K ∩ U))) :
    let P := fun z => twoPlaneProjection (G z) (residualRealColumn (q z))
      (residualImagColumn (q z))
    ContinuousOn P K ∧
      (∀ z ∈ U, P z = twoPlaneProjection (G z) (fderiv ℝ H z 1) (fderiv ℝ H z I)) ∧
      MemLp (fun z => fderiv ℝ P z v) 2 (volume.restrict (K ∩ U)) := by
  let a := fun z => residualRealColumn (q z)
  let b := fun z => residualImagColumn (q z)
  have ha : ContinuousOn a K := residualRealColumn.continuous.comp_continuousOn hq
  have hb : ContinuousOn b K := residualImagColumn.continuous.comp_continuousOn hq
  have ha1 : ContDiffOn ℝ 1 a U := residualRealColumn.contDiff.comp_contDiffOn hq1
  have hb1 : ContDiffOn ℝ 1 b U := residualImagColumn.contDiff.comp_contDiffOn hq1
  have hc (z : ℂ) (hz : z ∈ U) : G z (a z) (b z) = 0 ∧
      G z (b z) (b z) = G z (a z) (a z) := by
    obtain ⟨s, hs, hf⟩ := hfactor z hz
    obtain ⟨hca, hcb⟩ := residual_columns_complexGradient H z
    rw [hf] at hca hcb
    exact residual_columns_conformal_of_smul (G z) (hGsymm z (hUK hz)) hs (q z)
      (by simpa only [hca, hcb] using (hconf z hz).1)
      (by simpa only [hca, hcb] using (hconf z hz).2)
  have hcross : EqOn (fun z => G z (a z) (b z)) (fun _ => 0) K :=
    (show EqOn (fun z => G z (a z) (b z)) (fun _ => 0) U from
      fun z hz => (hc z hz).1).of_subset_closure
        ((hG.clm_apply ha).clm_apply hb) continuousOn_const hUK hKU
  have hdiag : EqOn (fun z => G z (b z) (b z)) (fun z => G z (a z) (a z)) K :=
    (show EqOn (fun z => G z (b z) (b z)) (fun z => G z (a z) (a z)) U from
      fun z hz => (hc z hz).2).of_subset_closure
        ((hG.clm_apply hb).clm_apply hb) ((hG.clm_apply ha).clm_apply ha) hUK hKU
  have hpos (z : ℂ) (hz : z ∈ K) : 0 < G z (a z) (a z) :=
    residual_columns_factor_pos (G z) (hGpos z hz) (hqne z hz) (hdiag hz)
  have hP : ContinuousOn (fun z => twoPlaneProjection (G z) (a z) (b z)) K := by
    let L := ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))
    have hA : ContinuousOn (fun z => (G z (a z)).smulRight (a z)) K :=
      (L.continuous.comp_continuousOn (hG.clm_apply ha)).clm_apply ha
    have hB : ContinuousOn (fun z => (G z (b z)).smulRight (b z)) K :=
      (L.continuous.comp_continuousOn (hG.clm_apply hb)).clm_apply hb
    exact (((hG.clm_apply ha).clm_apply ha).inv₀ (fun z hz => (hpos z hz).ne')).smul
      (hA.add hB)
  have hpart (L : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      MemLp (fun z => fderiv ℝ (fun w => L (q w)) z v) 2 (volume.restrict (K ∩ U)) := by
    apply (L.comp_memLp' hdq).ae_eq
    filter_upwards [ae_restrict_mem (hK.measurableSet.inter hU.measurableSet)] with z hz
    have hh := L.hasFDerivAt.comp z
      ((hq1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero).hasFDerivAt
    exact (congrArg (fun D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin n) => D v) hh.fderiv).symm
  refine ⟨hP, ?_, twoPlaneProjection_derivative_memLp hK hU hG ha hb hG1 ha1 hb1
    (fun z hz => (hpos z hz).ne') v hdG (hpart residualRealColumn) (hpart residualImagColumn)⟩
  intro z hz
  obtain ⟨s, hs, hf⟩ := hfactor z hz
  exact residual_projection_eq_of_gradient_factor (G z) (hGsymm z (hUK hz)) hs hf
    (hconf z hz).1 (hconf z hz).2

end PoincareConjecture.M65Branch
