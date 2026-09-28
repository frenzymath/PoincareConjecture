import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarPullback
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarScaling
import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

theorem scalar_evolution_eq_of_metric_isometry
    {n : ℕ} {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] [T2Space N]
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (hf : MetricHomothety g h f 1)
    (hscalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D'.scalarCurvature) (x : M) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x) := by
  have hS : D.scalarCurvature = D'.scalarCurvature ∘ f := by
    funext y
    symm
    simpa only [div_one, Function.comp_apply] using
      M13.homothety_scalarCurvature_eq g h f 1 zero_lt_one hf D D' y
  have hR : D'.ricciNormSq (f x) = D.ricciNormSq x := by
    simpa only [one_pow, div_one] using
      homothety_ricciNormSq_eq g h f 1 zero_lt_one hf D D' x
  rw [hS, D.laplacian_comp_of_metric_pullback D' f.contMDiffAt
    (Eventually.of_forall fun y => M13.diffeomorph_mfderiv_isInvertible f y)
    (Eventually.of_forall fun y v w => by simpa only [one_mul] using (hf y v w).symm)
    (hscalar (f x)), hR]

theorem regularSlab_metricHomothety (F : SurgeryFlowData.{u})
    {a b : ℝ} (S : SurgeryRegularSlab F.slice F.metric a b) (t : Icc a b) :
    MetricHomothety (S.flow.metric t.1) (F.metric t.1) (S.identify t) 1 := by
  intro x v w
  simpa only [one_mul] using S.metric_pullback t x v w

theorem regularSlab_scalar_eq (F : SurgeryFlowData.{u})
    {a b : ℝ} (S : SurgeryRegularSlab F.slice F.metric a b)
    (t : Icc a b) (x : (F.slice a).carrier) :
    (F.connection t.1).scalarCurvature (S.identify t x) =
      (S.flow.connection t.1).scalarCurvature x := by
  simpa only [div_one] using M13.homothety_scalarCurvature_eq
    (S.flow.metric t.1) (F.metric t.1) (S.identify t) 1 zero_lt_one
    (regularSlab_metricHomothety F S t) (S.flow.connection t.1) (F.connection t.1) x

theorem regularSlab_scalar_evolution_eq (P : M44CapPersistencePredecessors.{u})
    (F : SurgeryFlowData.{u}) {a b : ℝ} (S : SurgeryRegularSlab F.slice F.metric a b)
    (t : Icc a b) (x : (F.slice a).carrier) :
    (S.flow.connection t.1).laplacian (S.flow.connection t.1).scalarCurvature x +
        2 * (S.flow.connection t.1).ricciNormSq x =
      (F.connection t.1).laplacian (F.connection t.1).scalarCurvature (S.identify t x) +
        2 * (F.connection t.1).ricciNormSq (S.identify t x) :=
  scalar_evolution_eq_of_metric_isometry (S.flow.connection t.1) (F.connection t.1)
    (S.identify t) (regularSlab_metricHomothety F S t)
    (scalar_smooth_of_predecessors P (F.connection t.1)) x

end PoincareConjecture.M44
