import PoincareConjecture.Proofs.M35.RawFlow.AxisTimeCoefficients










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1



theorem rotational_axis_angular_ricci
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {r : ℝ} (hr : 0 < r) :
    D.ricci (r • e 2) (e 0) (e 0) = radialTangentialCurvatureFactor g r +
      axisAngularCoefficient g r * radialMixedCurvatureFactor g r / axisRadialCoefficient g r := by
  let p := r • e 2
  let w : Fin 3 → ℝ :=
    ![axisAngularCoefficient g r, axisAngularCoefficient g r, axisRadialCoefficient g r]
  let b : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) p) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hb (i : Fin 3) : b i = e i := EuclideanSpace.basisFun_apply (Fin 3) ℝ i
  have hgram : Matrix.of (fun i j : Fin 3 => g.inner p (b i) (b j)) = Matrix.diagonal w := by
    ext i j
    simp only [Matrix.of_apply, p, hb, rotational_axis_metric g hrotation]
    fin_cases i <;> fin_cases j <;> simp [e, w, Matrix.diagonal]
  have hw (i : Fin 3) : w i ≠ 0 := by
    fin_cases i
    · exact (axisAngularCoefficient_pos g r).ne'
    · exact (axisAngularCoefficient_pos g r).ne'
    · exact (axisRadialCoefficient_pos g r).ne'
  have hunit : IsUnit w := Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hw i))
  have hinv (i : Fin 3) : Ring.inverse w i = (w i)⁻¹ := by
    have h := congrFun (Ring.inverse_mul_cancel w hunit) i
    rw [← one_div]
    exact (eq_div_iff (hw i)).mpr h
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor p
  have hricci : D.ricci p (e 0) (e 0) =
      ∑ j : Fin 3, (w j)⁻¹ * D.curvatureTensor p (e 0) (b j) (e 0) (b j) := by
    rw [D.ricci_eq_inverse_gram p b A hA (e 0) (e 0), hgram, Matrix.inv_diagonal]
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hinv]
  obtain ⟨h01, h02, _⟩ := rotational_sectional_numerators_axis D hrotation hr
  rw [hricci]
  simp only [hb, Fin.sum_univ_succ, Fin.sum_univ_zero]
  erw [h01, h02]
  simp only [D.curvatureTensor_zero_first, mul_zero, zero_add, add_zero,
    w, Matrix.cons_val_zero, Matrix.cons_val_succ]
  field_simp [(axisAngularCoefficient_pos g r).ne', (axisRadialCoefficient_pos g r).ne']



theorem raw_axisWarpingRadius_hasDerivWithinAt_intrinsic
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
            (G.flow.metric t).inner x u v)
    {r : ℝ} (hr : 0 < r) :
    HasDerivWithinAt (fun s => axisWarpingRadius (G.flow.metric s) r)
      (axisWarpingSecond (G.flow.metric t) r +
        (axisWarpingSlope (G.flow.metric t) r ^ 2 - 1) /
          axisWarpingRadius (G.flow.metric t) r) (Ico 0 G.lifetime) t := by
  let g := G.flow.metric t
  have heq : -r * (G.flow.connection t).ricci (r • e 2) (e 0) (e 0) /
      Real.sqrt (axisAngularCoefficient g r) =
        axisWarpingSecond g r + (axisWarpingSlope g r ^ 2 - 1) / axisWarpingRadius g r := by
    rw [rotational_axis_angular_ricci (G.flow.connection t) hrotation hr]
    calc
      _ = -axisWarpingRadius g r *
          (radialTangentialCurvatureFactor g r / axisAngularCoefficient g r +
            radialMixedCurvatureFactor g r / axisRadialCoefficient g r) := by
        change -r * (radialTangentialCurvatureFactor g r +
            axisAngularCoefficient g r * radialMixedCurvatureFactor g r /
              axisRadialCoefficient g r) / Real.sqrt (axisAngularCoefficient g r) = _
        unfold axisWarpingRadius
        field_simp [(axisAngularCoefficient_pos g r).ne',
          (axisRadialCoefficient_pos g r).ne',
          (Real.sqrt_pos.mpr (axisAngularCoefficient_pos g r)).ne']
        rw [Real.sq_sqrt (axisAngularCoefficient_pos g r).le]
        ring
      _ = _ := by
        rw [radialTangentialCurvatureFactor_eq_warping g hr,
          radialMixedCurvatureFactor_eq_warping g hr]
        field_simp [(axisWarpingRadius_pos g hr).ne']
        ring
  rw [← heq]
  exact raw_axisWarpingRadius_hasDerivWithinAt G ht r

end PoincareConjecture.M35.Uniqueness
