import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Model.LinearRechart
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.Coordinates.FinSucc

open Set
open scoped Manifold ContDiff Bundle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.RiemannianMetric
def realLineMetric : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,ℝ) ∞ ℝ
    (TangentSpace 𝓘(ℝ,ℝ) : ℝ → Type _) :=
  { riemannianMetricVectorSpace ℝ with
    contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le le_top }

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
local instance lineProductRawChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (M × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin n)) M ℝ ℝ

def lineModelEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  (ContinuousLinearEquiv.prodComm ℝ _ _).trans (Poincare.EuclideanSpace.euclideanConsCLE n)

@[instance_reducible]
def lineProductChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) (M × ℝ) :=
  Poincare.Manifold.linearRechart (M := M × ℝ) (lineModelEquiv n)

theorem lineProductIsManifold :
    let := lineProductChartedSpace (n := n) (M := M)
    IsManifold (𝓡 (n+1)) ∞ (M × ℝ) := by
  let : IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n) × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓘(ℝ,ℝ)) M ℝ
  exact Poincare.Manifold.isManifold_linearRechart (M := M × ℝ) (lineModelEquiv n)

def lineProductDiffeomorph :
    let := lineProductChartedSpace (n := n) (M := M)
    (M × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ,ℝ), 𝓡 (n+1)⟯ (M × ℝ) := by
  let : IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n) × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓘(ℝ,ℝ)) M ℝ
  let := lineProductChartedSpace (n := n) (M := M)
  simpa only [modelWithCornersSelf_prod] using
    Poincare.Manifold.linearRechartDiffeomorph (M := M × ℝ) (lineModelEquiv n)

def lineProduct (g : PoincareConjecture.RiemannianMetric n M) :
    let := lineProductChartedSpace (n := n) (M := M)
    let := lineProductIsManifold (n := n) (M := M)
    PoincareConjecture.RiemannianMetric (n+1) (M × ℝ) := by
  let := lineProductChartedSpace (n := n) (M := M)
  let := lineProductIsManifold (n := n) (M := M)
  let e := lineProductDiffeomorph (n := n) (M := M)
  apply Induced.pullbackMetric (product g realLineMetric) e.symm e.symm.contMDiff
  intro x
  have hh := mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) (e.symm x))
    (e.symm.contMDiff.mdifferentiable (by simp) x)
  have hid : (e : M × ℝ → M × ℝ) ∘ e.symm = id := funext e.apply_symm_apply
  rw [hid, mfderiv_id] at hh
  exact Function.LeftInverse.injective (fun v => (congrArg (fun L => L v) hh).symm)

theorem lineProduct_inner (g : PoincareConjecture.RiemannianMetric n M) :
    let := lineProductChartedSpace (n := n) (M := M)
    let := lineProductIsManifold (n := n) (M := M)
    let e := lineProductDiffeomorph (n := n) (M := M)
    ∀ (z : M × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ,ℝ)) z),
      (lineProduct g).inner (e z)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z w) =
      g.inner z.1 v.1 w.1 + v.2 * w.2 := by
  let := lineProductChartedSpace (n := n) (M := M)
  let := lineProductIsManifold (n := n) (M := M)
  let e := lineProductDiffeomorph (n := n) (M := M)
  dsimp only
  intro z v w
  have hh := mfderiv_comp z (e.symm.contMDiff.mdifferentiable (by simp) (e z))
    (e.contMDiff.mdifferentiable (by simp) z)
  have hid : (e.symm : M × ℝ → M × ℝ) ∘ e = id := funext e.symm_apply_apply
  rw [hid, mfderiv_id] at hh
  change (product g realLineMetric).inner (e.symm (e z))
    (mfderiv (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ,ℝ)) e.symm (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v))
    (mfderiv (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ,ℝ)) e.symm (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z w)) = _
  have hv := congrArg (fun L => L v) hh
  have hw := congrArg (fun L => L w) hh
  change v = mfderiv (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ,ℝ)) e.symm (e z)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v) at hv
  change w = mfderiv (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ,ℝ)) e.symm (e z)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z w) at hw
  rw [← hv, ← hw, e.symm_apply_apply, product_inner]
  change g.inner z.1 v.1 w.1 + inner ℝ v.2 w.2 = _
  simp only [RCLike.inner_apply, conj_trivial]
  ring
end PoincareConjecture.RiemannianMetric
