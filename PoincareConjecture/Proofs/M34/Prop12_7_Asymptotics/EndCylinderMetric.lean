import PoincareConjecture.Proofs.M34.Standard.EndExhaustion
import PoincareConjecture.Proofs.M34.Mathlib.RiemannianMetricExt
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



noncomputable def endCylinderParameter (t : ℝ) : ℝ :=
  if t ∈ Ico 0 1 then t else 0



theorem endCylinderParameter_nonneg (t : ℝ) : 0 ≤ endCylinderParameter t := by
  unfold endCylinderParameter
  split_ifs with ht
  · exact ht.1
  · exact le_rfl



theorem endCylinderParameter_lt_one (t : ℝ) : endCylinderParameter t < 1 := by
  unfold endCylinderParameter
  split_ifs with ht
  · exact ht.2
  · norm_num



noncomputable def endCylinderAxial (e : StandardCylindricalEnd g) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  (fderiv ℝ (endExhaustion e) x).smulRight (fderiv ℝ (endExhaustion e) x)



noncomputable def endCylinderCoefficients (e : StandardCylindricalEnd g) (s : ℝ)
    (x : StandardCapSpace) : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  (1 - s) • g.euclideanCoefficients x + s • endCylinderAxial e x



theorem endCylinderCoefficients_apply (e : StandardCylindricalEnd g) (s : ℝ)
    (x u v : StandardCapSpace) :
    endCylinderCoefficients e s x u v = (1 - s) * g.inner x u v +
      s * (fderiv ℝ (endExhaustion e) x u * fderiv ℝ (endExhaustion e) x v) := by
  simp only [endCylinderCoefficients, endCylinderAxial, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rfl



theorem endCylinderAxial_contDiff (e : StandardCylindricalEnd g) :
    ContDiff ℝ ∞ (endCylinderAxial e) := by
  have hf : ContDiff ℝ ∞ (endExhaustion e) :=
    contMDiff_iff_contDiff.mp (endExhaustion_contMDiff e)
  have hd := hf.fderiv_right (m := ∞) (by simp)
  exact hd.smulRight hd



theorem endCylinderCoefficients_contDiff (e : StandardCylindricalEnd g) :
    ContDiff ℝ ∞ (fun z : ℝ × StandardCapSpace => endCylinderCoefficients e z.1 z.2) := by
  have : IsBoundedSMul ℝ (StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul
      (𝕜 := ℝ) (E := StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ)
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  exact ((contDiff_const.sub contDiff_fst).smul
    (hg.comp contDiff_snd)).add
      (contDiff_fst.smul ((endCylinderAxial_contDiff e).comp contDiff_snd))



theorem endCylinderCoefficients_pos (e : StandardCylindricalEnd g)
    {s : ℝ} (hs : s ∈ Ico 0 1) (x u : StandardCapSpace) (hu : u ≠ 0) :
    0 < endCylinderCoefficients e s x u u := by
  rw [endCylinderCoefficients_apply]
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hs.2) (g.pos x u hu))
    (mul_nonneg hs.1 (mul_self_nonneg _))




noncomputable def endCylinderAuxMetric (e : StandardCylindricalEnd g) (t : ℝ) :
    RiemannianMetric 3 StandardCapSpace :=
  RiemannianMetric.ofEuclideanCoefficients (endCylinderCoefficients e (endCylinderParameter t))
    ((endCylinderCoefficients_contDiff e).comp (contDiff_const.prodMk contDiff_id))
    (fun x u v => by rw [endCylinderCoefficients_apply, endCylinderCoefficients_apply,
      g.symm x u v]; ring)
    (endCylinderCoefficients_pos e ⟨endCylinderParameter_nonneg t,
      endCylinderParameter_lt_one t⟩)



theorem endCylinderAuxMetric_inner (e : StandardCylindricalEnd g) {t : ℝ}
    (ht : t ∈ Ico 0 1) (x u v : StandardCapSpace) :
    (endCylinderAuxMetric e t).inner x u v = endCylinderCoefficients e t x u v := by
  change endCylinderCoefficients e (endCylinderParameter t) x u v = _
  simp only [endCylinderParameter, ht, if_true]



theorem endCylinderAuxMetric_zero (e : StandardCylindricalEnd g) :
    endCylinderAuxMetric e 0 = g := by
  apply Bundle.ContMDiffRiemannianMetric.eq_of_inner_eq
  intro x
  ext u v
  rw [endCylinderAuxMetric_inner e (by norm_num), endCylinderCoefficients_apply]
  simp



theorem endCylinderAuxMetric_smooth (e : StandardCylindricalEnd g) :
    RiemannianMetric.IsSmoothFamilyOn (endCylinderAuxMetric e) (Ico 0 1) := by
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart (fun _ _ => rfl)
    (endCylinderAuxMetric e) (fun z => endCylinderCoefficients e z.1 z.2)
  · have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × StandardCapSpace) ∞
        (fun p : ℝ × StandardCapSpace => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact (endCylinderCoefficients_contDiff e).contDiffOn.contMDiffOn.comp
      hmap.contMDiffOn (fun _ hp => hp)
  · intro t ht x u v
    exact endCylinderAuxMetric_inner e ht x u v

end PoincareConjecture.M34
