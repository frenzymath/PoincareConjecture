import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal BigOperators

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


theorem two_le_dimension (K : AncientKappaSolution n M)
    (hcalculus : (K.flow.connection 0).CurvatureTensorCalculus) : 2 ≤ n := by
  by_contra hn
  obtain ⟨x, hx⟩ := K.nonflat 0 le_rfl
  apply hx
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
    finrank_euclideanSpace_fin
  have hcomponent (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      (K.flow.connection 0).curvatureTensor x
        ((K.flow.metric 0).orthonormalBasis x i)
        ((K.flow.metric 0).orthonormalBasis x j)
        ((K.flow.metric 0).orthonormalBasis x k)
        ((K.flow.metric 0).orthonormalBasis x l) = 0 := by
    have hkl : k = l := by
      apply Fin.ext
      have hk := k.isLt
      have hl := l.isLt
      omega
    subst l
    have hs := (hcalculus.2.2.2.1 x
      ((K.flow.metric 0).orthonormalBasis x i)
      ((K.flow.metric 0).orthonormalBasis x j)
      ((K.flow.metric 0).orthonormalBasis x k)
      ((K.flow.metric 0).orthonormalBasis x k)).1
    linarith
  simp [LeviCivitaData.curvatureTensorNorm, hcomponent]


theorem closed_cylinder_volume_lower_bound (K : AncientKappaSolution n M)
    (t : ℝ) (ht : t ≤ 0) (p : M) (r : ℝ) (hr : 0 < r)
    (hbound : ∀ s ∈ Icc (t - r ^ 2) t, ∀ q ∈ (K.flow.metric t).ball p r,
      (K.flow.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (K.kappa * r ^ n) ≤
      (K.flow.metric t).volumeMeasure ((K.flow.metric t).ball p r) := by
  rw [← calibratedMetricVolume_eq_volumeMeasure]
  apply K.noncollapsed r hr t ht p r hr le_rfl
  intro s hs q hq
  rw [abs_of_nonneg (show 0 ≤ (K.flow.connection s).curvatureTensorNorm q from
    Real.sqrt_nonneg _)]
  exact hbound s ⟨hs.1.le, hs.2⟩ q hq

end PoincareConjecture.AncientKappaSolution
