import PoincareConjecture.Proofs.M25.AppA_1_Necks.AmbientScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem realization_ricci_eq (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ)
    (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData h)
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V) (h0 : 0 ∈ V)
    (hstrip : ∀ x ∈ V, ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (heq : ∀ x ∈ V, h.euclideanCoefficients x = N.m25_normalizedEuclideanCoefficients q s x)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    D.ricci 0 v w = N.connection.ricci (N.coordinate_map (q, s))
      (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0 v)
      (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0 w) := by
  have hc : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let Dc := rescaledMetric_connection g N.connection (N.scale⁻¹ ^ 2) hc
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (N.euclideanParametrization q s) V :=
    fun x hx => (N.euclideanParametrization_contMDiffAt q s (hstrip x hx)).contMDiffWithinAt
  have hm (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ V)
      (a b : TangentSpace (𝓡 3) x) :
      h.inner x a b = (rescaledMetric g (N.scale⁻¹ ^ 2) hc).inner
        (N.euclideanParametrization q s x)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x a)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x b) := by
    change h.euclideanCoefficients x a b = _
    rw [heq x hx, rescaledMetric_inner]
    exact N.normalizedEuclideanCoefficients_pullback q s (hstrip x hx) a b
  have hricci := D.ricci_eq_of_local_isometry Dc hV hf hm h0 v w
  rw [rescaledMetric_ricci, N.euclideanParametrization_zero] at hricci
  exact hricci

end PoincareConjecture.EpsilonNeck
