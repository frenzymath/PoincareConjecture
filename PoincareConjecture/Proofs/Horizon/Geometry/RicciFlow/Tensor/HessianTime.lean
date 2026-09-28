import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.General
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.SpatialDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


lemma hasDerivAt_hessian_time
    (F : RicciFlow n M J) {f : ℝ × M → ℝ} {df : M → ℝ}
    {t : ℝ} (ht : t ∈ interior J)
    (hspace : ∀ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f (s, y)))
    (hreg : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, y))
    (hdf : ∀ y, HasDerivAt (fun s => f (s, y)) (df y) t)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let A := deriv (fun s => (F.connection s).connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t
    HasDerivAt (fun s => (F.connection s).hessian (fun y => f (s, y)) x u v)
      ((F.connection t).hessian df x u v -
        mvfderiv (𝓡 n) (fun y => f (t, y)) x (A u)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let T : ℝ → CovariantTensorEvaluation n M 1 := fun s => differentialEvaluation (fun y => f (s, y))
  let W : ℝ → CovariantTensorEvaluation n M 1 := fun _ => differentialEvaluation df
  have h := F.hasDerivAt_covariantTensorDerivative_time_all (T := T) (W := W) ht x
    (fun s => differentialEvaluation_isSmooth (hspace s))
    (fun y X hX => Poincare.Manifold.contMDiffAt_mvfderiv_spatial (hreg y) (hX 0))
    (fun y z => Poincare.Manifold.hasDerivAt_mvfderiv_time (hreg y) hdf (z 0)) u ![v]
  simpa only [T, W, Matrix.Fin.cons_vecCons, Fin.sum_univ_one,
    ← LeviCivitaData.hessian_eq_covariantTensorDerivative,
    differentialEvaluation, Function.update_self, Matrix.cons_val_zero] using h

private lemma scalarCurvature_smooth
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  intro x
  have h := (hD.2.1.tensorTrace (g := g)).contMDiffAt_apply
    (x := x) (X := fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
  convert h using 1
  funext y
  unfold RiemannianMetric.tensorTrace LeviCivitaData.scalarCurvature
  apply Finset.sum_congr rfl
  intro i _
  rfl



lemma hasDerivAt_hessian_scalarCurvature
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let D := F.connection t
    let A := deriv (fun s => (F.connection s).connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t
    HasDerivAt (fun s => (F.connection s).hessian (F.connection s).scalarCurvature x u v)
      (D.hessian (fun y => D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y) x u v -
        mvfderiv (𝓡 n) D.scalarCurvature x (A u)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have hspace (s : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F.connection s).scalarCurvature :=
    scalarCurvature_smooth (n := n) (M := M) (g := F.metric s) (F.connection s)
      (hC.tensor_calculus n M (F.metric s) (F.connection s))
  dsimp only
  refine F.hasDerivAt_hessian_time
    (f := fun p => (F.connection p.1).scalarCurvature p.2)
    (df := fun y => (F.connection t).laplacian (F.connection t).scalarCurvature y +
      2 * (F.connection t).ricciNormSq y) ht
    hspace
    ?_ ?_ x u v
  · intro y
    exact (hC.scalar_regular n M J F (t, y) ⟨interior_subset ht, Set.mem_univ y⟩).contMDiffAt
      (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) Filter.univ_mem)
  · intro y
    exact (hC.scalar_evolution n M J F t (interior_subset ht) y).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)



lemma hasDerivAt_hessian_scalarCurvature_contractions
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => (F.connection s).hessian (F.connection s).scalarCurvature x u v)
      (D.hessian (fun y => D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y) x u v +
        ∑ i, (D.covariantTensorDerivative D.ricciEvaluation x ![u, v, b i] +
          D.covariantTensorDerivative D.ricciEvaluation x ![v, u, b i] -
          D.covariantTensorDerivative D.ricciEvaluation x ![b i, u, v]) *
            mvfderiv (𝓡 n) D.scalarCurvature x (b i)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let A := deriv (fun s => (F.connection s).connection
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have h := F.hasDerivAt_hessian_scalarCurvature hC ht x u v
  have hexp := congrArg (mvfderiv (𝓡 n) D.scalarCurvature x) (b.sum_repr' (A u))
  simp only [map_sum, map_smul, smul_eq_mul] at hexp
  have hcoef (i) : inner ℝ (b i) (A u) =
      -D.covariantTensorDerivative D.ricciEvaluation x ![u, v, b i] -
        D.covariantTensorDerivative D.ricciEvaluation x ![v, u, b i] +
        D.covariantTensorDerivative D.ricciEvaluation x ![b i, u, v] := by
    rw [real_inner_comm]
    exact F.inner_deriv_connection_extend ht hD x u v (b i)
  simp only [hcoef] at hexp
  apply h.congr_deriv
  rw [← hexp, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end PoincareConjecture.RicciFlow
