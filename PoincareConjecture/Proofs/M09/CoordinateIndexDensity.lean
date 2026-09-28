import PoincareConjecture.Proofs.M09.CoordinateConnectionBilinear








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def coordinateScalarPartial (R : ℝ × E → ℝ) (z : ℝ × E) : E →L[ℝ] ℝ :=
  (fderiv ℝ R z).comp (ContinuousLinearMap.inr ℝ ℝ E)

noncomputable def coordinateMetricTimePartial (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ G z (1, 0)

noncomputable def coordinateIndexCurvature (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (u v w : E) : E :=
  let C := coordinateConnectionBilinear G
  fderiv ℝ C z (0, u) v w - fderiv ℝ C z (0, v) u w +
    C z u (C z v w) - C z v (C z u w)

noncomputable def coordinateIndexHessian (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (z : ℝ × E) (v w : E) : ℝ :=
  fderiv ℝ (coordinateScalarPartial R) z (0, v) w -
    coordinateScalarPartial R z (coordinateConnectionBilinear G z v w)

noncomputable def coordinateTimeCovariant (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (u v w : E) : ℝ :=
  let H := coordinateMetricTimePartial G
  let C := coordinateConnectionBilinear G
  fderiv ℝ H z (0, u) v w - H z (C z u v) w - H z v (C z u w)

noncomputable def coordinateIndexDensity (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (R : ℝ × E → ℝ) (z : ℝ × E) (a v w : E) : ℝ :=
  G z w w + G z (coordinateIndexCurvature G z v a v) a +
    2 * z.1 ^ 2 * coordinateIndexHessian G R z v v -
    coordinateTimeCovariant G z v a v + coordinateTimeCovariant G z a v v / 2

set_option maxHeartbeats 600000 in

theorem coordinateIndexDensity_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ)
    (Ω : Set (ℝ × E)) (hΩ : IsOpen Ω) (hG : ContDiffOn ℝ ∞ G Ω)
    (hR : ContDiffOn ℝ ∞ R Ω)
    (hpos : ∀ z ∈ Ω, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (U : Set P) (z : P → ℝ × E) (a v w : P → E)
    (hz : ContDiffOn ℝ ∞ z U) (ha : ContDiffOn ℝ ∞ a U)
    (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) (hzΩ : Set.MapsTo z U Ω) :
    ContDiffOn ℝ ∞ (fun x ↦ coordinateIndexDensity G R (z x) (a x) (v x) (w x)) U := by
  let C := coordinateConnectionBilinear G
  let H := coordinateMetricTimePartial G
  let Q := coordinateScalarPartial R
  have hC : ContDiffOn ℝ ∞ C Ω := coordinateConnectionBilinear_contDiffOn G Ω hΩ hG hpos
  have hH : ContDiffOn ℝ ∞ H Ω :=
    (hG.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hQ : ContDiffOn ℝ ∞ Q Ω :=
    (hR.fderiv_of_isOpen hΩ (by simp)).clm_comp contDiffOn_const
  have hDC := (hC.fderiv_of_isOpen hΩ (m := ∞) (by simp)).comp hz hzΩ
  have hDH := (hH.fderiv_of_isOpen hΩ (m := ∞) (by simp)).comp hz hzΩ
  have hDQ := (hQ.fderiv_of_isOpen hΩ (m := ∞) (by simp)).comp hz hzΩ
  have hCz := hC.comp hz hzΩ
  have hHz := hH.comp hz hzΩ
  have hQz := hQ.comp hz hzΩ
  have hGz := hG.comp hz hzΩ
  have hcurv : ContDiffOn ℝ ∞
      (fun x ↦ coordinateIndexCurvature G (z x) (v x) (a x) (v x)) U := by
    exact (((((hDC.clm_apply (contDiffOn_const.prodMk hv)).clm_apply ha).clm_apply hv).sub
      (((hDC.clm_apply (contDiffOn_const.prodMk ha)).clm_apply hv).clm_apply hv)).add
      ((hCz.clm_apply hv).clm_apply ((hCz.clm_apply ha).clm_apply hv))).sub
      ((hCz.clm_apply ha).clm_apply ((hCz.clm_apply hv).clm_apply hv))
  have hhess : ContDiffOn ℝ ∞
      (fun x ↦ coordinateIndexHessian G R (z x) (v x) (v x)) U :=
    ((hDQ.clm_apply (contDiffOn_const.prodMk hv)).clm_apply hv).sub
      (hQz.clm_apply ((hCz.clm_apply hv).clm_apply hv))
  have hcov (u v w : P → E) (hu : ContDiffOn ℝ ∞ u U)
      (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
      ContDiffOn ℝ ∞ (fun x ↦ coordinateTimeCovariant G (z x) (u x) (v x) (w x)) U :=
    ((((hDH.clm_apply (contDiffOn_const.prodMk hu)).clm_apply hv).clm_apply hw).sub
      ((hHz.clm_apply ((hCz.clm_apply hu).clm_apply hv)).clm_apply hw)).sub
      ((hHz.clm_apply hv).clm_apply ((hCz.clm_apply hu).clm_apply hw))
  exact (((((hGz.clm_apply hw).clm_apply hw).add
      ((hGz.clm_apply hcurv).clm_apply ha)).add
      ((contDiffOn_const.mul (hz.fst.pow 2)).mul hhess)).sub (hcov v a v hv ha hv)).add
      ((hcov a v v ha hv hv).div_const 2)

end PoincareConjecture.Proofs.M09
