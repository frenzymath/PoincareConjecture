import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Compact
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundModelCurvature
import PoincareConjecture.Proofs.M34.Standard.CompactCompleteness
import PoincareConjecture.Definitions.Ch11.SingularLimits









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)


theorem terminalCurvature_ricci_of_sectional_one
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1)
    (x : M) (v : TangentSpace (𝓡 3) x) : D.ricci x v v = 2 * g.inner x v v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hunit (i) : g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    simp
  have hsum := b.sum_inner_mul_inner v v
  change (∑ i, g.inner x v (b i) * g.inner x (b i) v) = g.inner x v v at hsum
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by simp [TangentSpace]
  calc
    D.ricci x v v = ∑ i, (g.inner x v v - g.inner x (b i) v * g.inner x v (b i)) := by
      change (∑ i, D.curvatureTensor x v (b i) v (b i)) = _
      simp only [M44.curvatureTensor_eq_metricGram_of_sectional_one D hsec, hunit, mul_one]
    _ = 3 * g.inner x v v - g.inner x v v := by
      rw [Finset.sum_sub_distrib]
      simp_rw [mul_comm (g.inner x (b _) v)]
      rw [hsum]
      simp [hdim]
    _ = 2 * g.inner x v v := by ring



theorem terminalCurvature_round_model_distance
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)
    (p x : N.model.carrier) :
    N.model_metric.edist p x ≤ ENNReal.ofReal (Real.sqrt 15) := by
  let : CompactSpace N.model.carrier := ⟨N.model_compact⟩
  let : PreconnectedSpace N.model.carrier := ⟨N.model_connected.isPreconnected⟩
  have hRic (y : N.model.carrier) (v : TangentSpace (𝓡 3) y) :
      2 * N.model_metric.inner y v v ≤ N.model_connection.ricci y v v :=
    (terminalCurvature_ricci_of_sectional_one N.model_connection N.model_curvature_one y v).ge
  have hd := N.model_metric.edist_le_of_positive_ricci N.model_connection
    N.model_metric.metricComplete_of_compact (by norm_num : (0 : ℝ) < 2) hRic p x
  norm_num at hd ⊢
  exact hd

end PoincareConjecture.M47
