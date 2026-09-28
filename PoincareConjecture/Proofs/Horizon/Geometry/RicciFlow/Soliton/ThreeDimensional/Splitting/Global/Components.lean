import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciNullity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem connectedComponent_complete_parallel_coordinate
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : RiemannianMetric.HasUnitGradient D f)
    (hzero : RiemannianMetric.HasZeroHessian D f)
    (hc : MetricComplete g) (p : M) :
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    let gC := g.connectedComponentMetric p
    let fC : C → ℝ := f ∘ Subtype.val
    ConnectedSpace C ∧ MetricComplete gC ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ fC ∧
      RiemannianMetric.HasUnitGradient gC.leviCivitaData fC ∧
      RiemannianMetric.HasZeroHessian gC.leviCivitaData fC := by
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let gC := g.connectedComponentMetric p
  let DC := gC.leviCivitaData
  let incl : C → M := Subtype.val
  let fC : C → ℝ := f ∘ incl
  have hi : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ incl :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) C
  have hinv (x : C) : (mfderiv (𝓡 n) (𝓡 n) incl x).IsInvertible :=
    ⟨hi.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩
  have hmetric (x : C) (v w : TangentSpace (𝓡 n) x) :
      gC.inner x v w = g.inner (incl x)
        (mfderiv (𝓡 n) (𝓡 n) incl x v) (mfderiv (𝓡 n) (𝓡 n) incl x w) := rfl
  have hpush (x : C) :
      mfderiv (𝓡 n) (𝓡 n) incl x (DC.gradient fC x) = D.gradient f (incl x) := by
    rw [DC.gradient_comp_eq_mpullback D
      (hi.mdifferentiable (by simp) x) (hf.mdifferentiable (by simp) (incl x))
      (hinv x) (hmetric x)]
    exact (hinv x).self_apply_inverse _
  refine ⟨inferInstance, ?_, hf.comp hi.contMDiff, ?_, ?_⟩
  · exact RiemannianMetric.metricComplete_of_subtype_val isClosed_connectedComponent
      g gC hmetric hc
  · intro x
    change gC.inner x (DC.gradient fC x) (DC.gradient fC x) = 1
    rw [hmetric, hpush]
    exact hunit (incl x)
  · intro x v w
    change DC.hessian (f ∘ incl) x v w = 0
    rw [DC.hessian_comp_of_metric_pullback D (hi.contMDiff x)
      (Eventually.of_forall hinv) (Eventually.of_forall hmetric) (hf (incl x))]
    exact hzero (incl x) _ _

theorem restrictComponent_ricciNullity
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (p : M) (t : ℝ)
    (q : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
    ricciNullity ((F.restrictComponent p).connection t) q =
      ricciNullity (F.connection t) q.1 := by
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let hi := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) C
  let L := (hi.mfderivToContinuousLinearEquiv (by simp) q).toLinearEquiv
  have hric (v w : TangentSpace (𝓡 n) q) :
      ((F.restrictComponent p).connection t).ricci q v w =
        (F.connection t).ricci q.1 (L v) (L w) :=
    ((F.restrictComponent p).connection t).ricci_eq_of_local_isometry
      (F.connection t) isOpen_univ hi.contMDiff.contMDiffOn
      (fun _ _ _ _ => rfl) (mem_univ q) v w
  have hker : ricciKernel (F.connection t) q.1 =
      (ricciKernel ((F.restrictComponent p).connection t) q).map L.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_ricciKernel, mem_ricciKernel]
    constructor
    · intro hv w
      rw [hric, L.apply_symm_apply]
      exact hv _
    · intro hv w
      obtain ⟨z, rfl⟩ := L.surjective w
      have hz := hv z
      rw [hric, L.apply_symm_apply] at hz
      exact hz
  unfold ricciNullity
  rw [hker, LinearEquiv.finrank_map_eq]

end PoincareConjecture.RicciFlow.Splitting
