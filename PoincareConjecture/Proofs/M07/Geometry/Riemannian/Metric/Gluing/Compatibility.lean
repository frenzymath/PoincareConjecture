import PoincareConjecture.Proofs.M07.Topology.Gluing.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Descent

open PoincareConjecture Bundle
open scoped ContDiff Manifold Topology








noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Poincare.Gluing
universe u v w

theorem OverlapSystem.exists_unique_metric_of_transition_invariance
    {n : ℕ}
    {A : Type v} {P : A -> Type w}
    [forall i, TopologicalSpace (P i)]
    [forall i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [forall i, IsManifold (𝓡 n) ∞ (P i)]
    (D : OverlapSystem P)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (Quotient D.setoid)]
    [IsManifold (𝓡 n) ∞ (Quotient D.setoid)]
    (g : forall i, RiemannianMetric n (P i))
    (hq : forall i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (D.include i))
    (ht : forall i j, ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (D.transition i j) (D.transition i j).source)
    (hg : forall i j (p : P i), p ∈ (D.transition i j).source ->
      forall a b : TangentSpace (𝓡 n) p,
        (g i).inner p a b =
          (g j).inner (D.transition i j p)
            (mfderiv (𝓡 n) (𝓡 n) (D.transition i j) p a)
            (mfderiv (𝓡 n) (𝓡 n) (D.transition i j) p b)) :
    ∃! gQ : RiemannianMetric n (Quotient D.setoid),
      forall i (p : P i) (a b : TangentSpace (𝓡 n) p),
        (g i).inner p a b =
          gQ.inner (D.include i p)
            (mfderiv (𝓡 n) (𝓡 n) (D.include i) p a)
            (mfderiv (𝓡 n) (𝓡 n) (D.include i) p b) := by
  apply exists_unique_metric_of_covering_local_diffeomorphisms g D.include hq
  · intro q
    induction q using Quotient.inductionOn with
    | h p => exact ⟨p.1, p.2, rfl⟩
  · intro i j p p' heq a b a' b' ha hb
    obtain ⟨hp, he⟩ := (D.include_eq_iff i j p p').mp heq
    change D.transition i j p = p' at he
    subst p'
    have hnear : D.include j ∘ D.transition i j =ᶠ[𝓝 p] D.include i := by
      filter_upwards [(D.transition i j).open_source.mem_nhds hp] with x hx
      exact ((D.include_eq_iff i j x _).mpr ⟨hx, rfl⟩).symm
    have hdt := ((ht i j).contMDiffAt ((D.transition i j).open_source.mem_nhds hp)).mdifferentiableAt (by simp)
    have hderiv :
        (mfderiv (𝓡 n) (𝓡 n) (D.include j) (D.transition i j p)).comp
          (mfderiv (𝓡 n) (𝓡 n) (D.transition i j) p) =
        mfderiv (𝓡 n) (𝓡 n) (D.include i) p := by
      rw [← mfderiv_comp p ((hq j).mdifferentiable (by simp) _) hdt]
      exact hnear.mfderiv_eq
    let L : P j -> (EuclideanSpace ℝ (Fin n)) ≃L[ℝ] (EuclideanSpace ℝ (Fin n)) :=
      fun x => (hq j).mfderivToContinuousLinearEquiv (by simp) x
    have haeq : mfderiv (𝓡 n) (𝓡 n) (D.transition i j) p a = a' := by
      apply (L (D.transition i j p)).injective
      have hv := congrArg (fun f : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) => f a) hderiv
      exact hv.trans ha
    have hbeq : mfderiv (𝓡 n) (𝓡 n) (D.transition i j) p b = b' := by
      apply (L (D.transition i j p)).injective
      have hv := congrArg (fun f : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) => f b) hderiv
      exact hv.trans hb
    have hm := hg i j p hp a b
    simpa only [haeq, hbeq] using hm

end Poincare.Gluing
