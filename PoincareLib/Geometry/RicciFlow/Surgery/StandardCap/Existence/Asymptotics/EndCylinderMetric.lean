import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Limits.EndExhaustion
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Metric.RiemannianMetricExt
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension
import PoincareLib.Geometry.RicciFlow.MetricFamily.Coordinates

/-!
# An actual ambient metric extending the shrinking end cylinder

The coefficient field (1-s)*g + s*d rho tensor d rho is positive for
0<=s<1 and smooth on the whole original cap. Above height two it is the
literal cylinder at time s. Only its restriction to the reference end
will be asserted to solve Ricci flow. This is Proposition 12.7,
pp. 298-299 and canonical-cylinder-model.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- A total parameter in the positive metric range, equal to time on
the included interval (Proposition 12.7, pp. 298-299). -/
noncomputable def endCylinderParameter (t : ℝ) : ℝ :=
  if t ∈ Ico 0 1 then t else 0

/-- The total parameter is nonnegative
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderParameter_nonneg (t : ℝ) : 0 ≤ endCylinderParameter t := by
  unfold endCylinderParameter
  split_ifs with ht
  · exact ht.1
  · exact le_rfl

/-- The total parameter is strictly below the collapse value
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderParameter_lt_one (t : ℝ) : endCylinderParameter t < 1 := by
  unfold endCylinderParameter
  split_ifs with ht
  · exact ht.2
  · norm_num

/-- The squared height differential as an actual continuous bilinear form
(Proposition 12.7, pp. 298-299). -/
noncomputable def endCylinderAxial (e : StandardCylindricalEnd g) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  (fderiv ℝ (endExhaustion e) x).smulRight (fderiv ℝ (endExhaustion e) x)

/-- The ambient coefficient formula, smooth for every real parameter
(Proposition 12.7, pp. 298-299). -/
noncomputable def endCylinderCoefficients (e : StandardCylindricalEnd g) (s : ℝ)
    (x : StandardCapSpace) : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  (1 - s) • g.euclideanCoefficients x + s • endCylinderAxial e x

/-- Exact scalar evaluation of the ambient coefficient field
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderCoefficients_apply (e : StandardCylindricalEnd g) (s : ℝ)
    (x u v : StandardCapSpace) :
    endCylinderCoefficients e s x u v = (1 - s) * g.inner x u v +
      s * (fderiv ℝ (endExhaustion e) x u * fderiv ℝ (endExhaustion e) x v) := by
  simp only [endCylinderCoefficients, endCylinderAxial, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rfl

/-- The actual axial coefficient field is globally smooth
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderAxial_contDiff (e : StandardCylindricalEnd g) :
    ContDiff ℝ ∞ (endCylinderAxial e) := by
  have hf : ContDiff ℝ ∞ (endExhaustion e) :=
    contMDiff_iff_contDiff.mp (endExhaustion_contMDiff e)
  have hd := hf.fderiv_right (m := ∞) (by simp)
  exact hd.smulRight hd

/-- Joint ordinary smoothness of the unbranched coefficients
(Proposition 12.7, pp. 298-299). -/
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

/-- The coefficient field is positive for the whole chosen parameter
range, including time zero (Proposition 12.7, pp. 298-299). -/
theorem endCylinderCoefficients_pos (e : StandardCylindricalEnd g)
    {s : ℝ} (hs : s ∈ Ico 0 1) (x u : StandardCapSpace) (hu : u ≠ 0) :
    0 < endCylinderCoefficients e s x u u := by
  rw [endCylinderCoefficients_apply]
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hs.2) (g.pos x u hu))
    (mul_nonneg hs.1 (mul_self_nonneg _))

/-- A genuine globally positive metric extending each included cylinder
slice, without asserting an ambient flow equation
(Proposition 12.7, pp. 298-299). -/
noncomputable def endCylinderAuxMetric (e : StandardCylindricalEnd g) (t : ℝ) :
    RiemannianMetric 3 StandardCapSpace :=
  RiemannianMetric.ofEuclideanCoefficients (endCylinderCoefficients e (endCylinderParameter t))
    ((endCylinderCoefficients_contDiff e).comp (contDiff_const.prodMk contDiff_id))
    (fun x u v => by rw [endCylinderCoefficients_apply, endCylinderCoefficients_apply,
      g.symm x u v]; ring)
    (endCylinderCoefficients_pos e ⟨endCylinderParameter_nonneg t,
      endCylinderParameter_lt_one t⟩)

/-- Included-time ambient metrics have the unbranched coefficient field
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderAuxMetric_inner (e : StandardCylindricalEnd g) {t : ℝ}
    (ht : t ∈ Ico 0 1) (x u v : StandardCapSpace) :
    (endCylinderAuxMetric e t).inner x u v = endCylinderCoefficients e t x u v := by
  change endCylinderCoefficients e (endCylinderParameter t) x u v = _
  simp only [endCylinderParameter, ht, if_true]

/-- The actual initial ambient metric is the supplied metric record
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderAuxMetric_zero (e : StandardCylindricalEnd g) :
    endCylinderAuxMetric e 0 = g := by
  apply Bundle.ContMDiffRiemannianMetric.eq_of_inner_eq
  intro x
  ext u v
  rw [endCylinderAuxMetric_inner e (by norm_num), endCylinderCoefficients_apply]
  simp

/-- The ambient metric family is jointly smooth on the included
nonnegative time interval (Proposition 12.7, pp. 298-299). -/
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

end PoincareMT.M34
