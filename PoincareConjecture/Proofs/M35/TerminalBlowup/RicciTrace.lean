import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Proofs.M13.CurvatureContractions

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

theorem ricci_le_scalar_mul_inner_of_nonnegative_sectional
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x u v u v)
    (v : TangentSpace (𝓡 n) x) :
    D.ricci x v v ≤ D.scalarCurvature x * g.inner x v v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  by_cases hv : v = 0
  · subst v
    change M13.ricciLinear D x 0 0 ≤ _
    simp
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
      inv_mul_cancel₀ hnorm.ne']
  have horth : Orthonormal ℝ (fun z : ({w} : Set (TangentSpace (𝓡 n) x)) => z.val) := by
    rw [orthonormal_iff_ite]
    intro a b
    have ha : a.val = w := Set.mem_singleton_iff.mp a.property
    have hb : b.val = w := Set.mem_singleton_iff.mp b.property
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    simp only [hb, hab, ite_true, real_inner_self_eq_norm_sq, hw, one_pow]
  obtain ⟨s, b, hsub, hb⟩ := horth.exists_orthonormalBasis_extension
  let i : s := ⟨w, hsub (Set.mem_singleton w)⟩
  have hbi : b i = w := congrFun hb i
  have htrace : D.ricci x w w ≤ D.scalarCurvature x := by
    rw [M13.scalarCurvature_eq_sum_basis D x b, ← hbi]
    exact Finset.single_le_sum
      (fun j _ => M04.nonneg_ricci_of_nonnegativeSectionalAt D x hsec (b j))
      (Finset.mem_univ i)
  have hscaled : D.ricci x w w = ‖v‖⁻¹ ^ 2 * D.ricci x v v := by
    change M13.ricciLinear D x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, M13.ricciLinear_apply]
    ring
  have h := mul_le_mul_of_nonneg_left htrace (sq_nonneg ‖v‖)
  rw [hscaled] at h
  have hcancel : ‖v‖ ^ 2 * ‖v‖⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hnorm.ne', one_pow]
  rw [← mul_assoc, hcancel, one_mul] at h
  have hgv : g.inner x v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  rwa [mul_comm, ← hgv] at h

end PoincareConjecture.LeviCivitaData
