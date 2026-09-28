import PoincareConjecture.Proofs.M35.CapGeometry.UnitTimeCanonical
import PoincareConjecture.Proofs.M35.Thm12_28.StrongCanonicalScalar










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.OrdinaryRealization



theorem scalar_directional_pullback_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) (v : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v =
      mvfderiv (𝓡 3) (connection F t).scalarCurvature ((sliceDiffeomorph ht).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ht).symm x v) := by
  have hfun : (F.connection t).scalarCurvature =
      (connection F t).scalarCurvature ∘ (sliceDiffeomorph ht).symm :=
    funext (fun y => (scalar_eq P F ht y).symm)
  rw [hfun]
  exact mvfderiv_comp_apply x
    ((Proofs.M09.scalarCurvature_contMDiff P.curvature (connection F t)).mdifferentiable
      (by simp) _)
    ((sliceDiffeomorph ht).symm.contMDiff.mdifferentiable (by simp) _) v



theorem exists_unit_time_scalar_estimates (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀) :
    ∃ A H : ℝ, 0 < A ∧ 0 < H ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace, H ≤ (E.flow.connection t).scalarCurvature x →
      (∀ v : TangentSpace (𝓡 3) x, (E.flow.metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) (E.flow.connection t).scalarCurvature x v| ≤
          A * (E.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
      |(E.flow.connection t).laplacian (E.flow.connection t).scalarCurvature x +
          2 * (E.flow.connection t).ricciNormSq x| ≤
        A * ((E.flow.connection t).scalarCurvature x) ^ 2 := by
  obtain ⟨deltaU, hdeltaU, hunit⟩ := exists_unit_time_canonical_constants P
  obtain ⟨deltaS, A, hdeltaS, hA, hbounds⟩ := exists_strong_canonical_scalar_bounds P
  let epsilon := min deltaS deltaU
  have he : 0 < epsilon := lt_min hdeltaS hdeltaU
  obtain ⟨C, H, _hC, hH, hcanonical⟩ := hunit epsilon he (min_le_right _ _) E
  refine ⟨max A C, H, hA.trans_le (le_max_left _ _), hH, ?_⟩
  intro t ht x hR
  have hb := hbounds epsilon C (min_le_left _ _) E.atlas g₀ E.flow t
    ((sliceDiffeomorph ht).symm x) (hcanonical t ht x hR)
  refine ⟨?_, hb.2⟩
  intro v hv
  have hunitv := (metric_pullback E.flow.base.flow ht x v v).trans hv
  have h := hb.1 (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ht).symm x v) hunitv
  have hscalar : ((generalizedFlow E.flow.base.flow).connection t).scalarCurvature
      ((sliceDiffeomorph ht).symm x) = (E.flow.connection t).scalarCurvature x :=
    scalar_eq P E.flow.base.flow ht x
  rw [hscalar] at h
  exact (congrArg abs (scalar_directional_pullback_eq P E.flow.base.flow ht x v)).trans_le h

end PoincareConjecture.M35.OrdinaryRealization
