import PoincareConjecture.Statements.M44Providers










set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

namespace OrdinaryParabolicRescaling

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain} {h a : ℝ}
  {hq : 0 < h⁻¹ ^ 2} (R : OrdinaryParabolicRescaling F (h⁻¹ ^ 2) hq a)



theorem cap_scalar_eq (s : ℝ) (x : M) :
    (R.flow.connection s).scalarCurvature x =
      h ^ 2 * (F.connection (a + s * h ^ 2)).scalarCurvature x := by
  have hscale : (R.flow.connection s).scalarCurvature x =
      h ^ 2 * (F.connection (parabolicTimeInv (h⁻¹ ^ 2) a s)).scalarCurvature x := by
    simpa only [Diffeomorph.coe_refl, id_eq, inv_pow, div_inv_eq_mul, mul_comm] using
      (R.metric_calculus s).scalar_eq
        (F.connection (parabolicTimeInv (h⁻¹ ^ 2) a s)) (R.flow.connection s) x
  apply hscale.trans
  apply congrArg (fun t => h ^ 2 * (F.connection t).scalarCurvature x)
  simp only [parabolicTimeInv, inv_pow, div_inv_eq_mul]



theorem cap_curvature_norm_eq (s : ℝ) (x : M) :
    (R.flow.connection s).curvatureTensorNorm x =
      h ^ 2 * (F.connection (a + s * h ^ 2)).curvatureTensorNorm x := by
  have hscale : (R.flow.connection s).curvatureTensorNorm x =
      h ^ 2 * (F.connection (parabolicTimeInv (h⁻¹ ^ 2) a s)).curvatureTensorNorm x := by
    simpa only [Diffeomorph.coe_refl, id_eq, inv_pow, div_inv_eq_mul, mul_comm] using
      (R.metric_calculus s).curvature_norm_eq
        (F.connection (parabolicTimeInv (h⁻¹ ^ 2) a s)) (R.flow.connection s) x
  apply hscale.trans
  apply congrArg (fun t => h ^ 2 * (F.connection t).curvatureTensorNorm x)
  simp only [parabolicTimeInv, inv_pow, div_inv_eq_mul]



theorem cap_canonical_threshold_iff (hh : 0 < h) (r s : ℝ) (x : M) :
    r⁻¹ ^ 2 ≤ (F.connection (a + s * h ^ 2)).scalarCurvature x ↔
      (h / r) ^ 2 ≤ (R.flow.connection s).scalarCurvature x := by
  rw [R.cap_scalar_eq]
  have hscale : (h / r) ^ 2 = h ^ 2 * r⁻¹ ^ 2 := by ring
  rw [hscale, mul_le_mul_iff_of_pos_left (sq_pos_of_pos hh)]



theorem cap_scalar_hasDerivAt {s d : ℝ} {x : M}
    (hd : HasDerivAt (fun t => (F.connection t).scalarCurvature x)
      d (a + s * h ^ 2)) :
    HasDerivAt (fun u => (R.flow.connection u).scalarCurvature x) (h ^ 4 * d) s := by
  have hclock : HasDerivAt (fun u : ℝ => a + u * h ^ 2) (h ^ 2) s := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id s).mul_const (h ^ 2)).const_add a
  have hscaled := (hd.comp s hclock).const_mul (h ^ 2)
  have hscalar : (fun u => (R.flow.connection u).scalarCurvature x) =
      fun u => h ^ 2 * (F.connection (a + u * h ^ 2)).scalarCurvature x :=
    funext fun u => R.cap_scalar_eq u x
  rw [hscalar]
  exact hscaled.congr_deriv (by ring)

end OrdinaryParabolicRescaling

end PoincareConjecture
