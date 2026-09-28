import PoincareConjecture.Proofs.M32.Claim11_35.NeckCovariantJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Realization

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

theorem exists_normalizedEuclideanCoefficients_scalar_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ 1 / 4 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ r : ℕ, r ≤ 4 → ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ r (fun x => N.normalizedEuclideanCoefficients q s x
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
          roundCylinderEuclideanCoefficients x
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤
          C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalized_pullback_covariant_fourJet_bound.{u}
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let A := max 1 ‖T.toContinuousLinearMap‖
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨C * A ^ 4, mul_pos hC (pow_pos (lt_of_lt_of_le zero_lt_one hA) _), ?_⟩
  intro M _ _ _ _ _ _ _ g N hε q s hs r hr i j
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j
  have heq : (fun x => E ((0, s) + T x)) =ᶠ[𝓝 0]
      (fun x => N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
    filter_upwards [N.normalizedEuclideanCoefficients_basis_eventuallyEq q hs i j]
      with x hx
    dsimp only [E, T]
    rw [hx, roundCylinderEuclideanCoefficients_basis q s]
  rw [← (heq.iteratedFDeriv ℝ r).self_of_nhds]
  have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    T (fun p => E ((0, s) + p)) r 0
  simp only [map_zero, iteratedFDeriv_comp_add_left, add_zero] at h
  have hpow : ‖T.toContinuousLinearMap‖ ^ r ≤ A ^ 4 :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) r).trans
      (pow_le_pow_right₀ hA hr)
  have hE : ‖iteratedFDeriv ℝ r E (0, s)‖ ≤ C * N.epsilon := by
    exact hbound N hε q hs r 0 (by omega) ![i, j]
  exact h.trans ((mul_le_mul hE hpow (pow_nonneg (norm_nonneg _) _)
    (mul_nonneg hC.le N.epsilon_pos.le)).trans_eq (by ring))

theorem exists_normalizedEuclideanCoefficients_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ 1 / 4 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ r : ℕ, r ≤ 4 →
        ‖iteratedFDeriv ℝ r (fun x => N.normalizedEuclideanCoefficients q s x -
          roundCylinderEuclideanCoefficients x) 0‖ ≤ C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedEuclideanCoefficients_scalar_fourJet_bound.{u}
  refine ⟨9 * C, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε q s hs r hr
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).reindex ((finRotate 3).symm)
  have hb (i : Fin 3) : b i = roundCylinderEuclideanBasis i := by
    simp only [b, roundCylinderEuclideanBasis, OrthonormalBasis.reindex_apply,
      Module.Basis.reindex_apply, OrthonormalBasis.coe_toBasis]
  have hN : ContDiffAt ℝ ∞ (N.normalizedEuclideanCoefficients q s) 0 :=
    N.normalizedEuclideanCoefficients_contDiffAt q s (by
      simpa only [map_zero, add_zero] using hs)
  have h := SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components b
    (hN.sub contDiff_roundCylinderEuclideanCoefficients.contDiffAt) r
    (C := C * N.epsilon) (fun i j => ?_)
  · convert h using 1
    ring
  · simpa only [sub_apply, hb] using hbound N hε q hs r hr i j

end PoincareConjecture.M32
