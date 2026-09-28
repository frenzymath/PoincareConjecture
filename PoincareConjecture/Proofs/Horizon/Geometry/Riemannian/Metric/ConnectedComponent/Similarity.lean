import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ConnectedComponent.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]


theorem connectedComponentMetric_inner_diffeomorph
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 m⟯ N) {a : ℝ}
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 m) e x v)
        (mfderiv (𝓡 n) (𝓡 m) e x w) = a * g.inner x v w)
    (p : M)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
    (v w : TangentSpace (𝓡 n) x) :
    (h.connectedComponentMetric (e p)).inner
        (Poincare.connectedComponentDiffeomorph e p x)
        (mfderiv (𝓡 n) (𝓡 m) (Poincare.connectedComponentDiffeomorph e p) x v)
        (mfderiv (𝓡 n) (𝓡 m) (Poincare.connectedComponentDiffeomorph e p) x w) =
      a * (g.connectedComponentMetric p).inner x v w := by
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let V := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) (e p)
  let E := Poincare.connectedComponentDiffeomorph e p
  have hchain (z : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 m) (𝓡 m) (Subtype.val : V → N) (E x)
        (mfderiv (𝓡 n) (𝓡 m) E x z) =
      mfderiv (𝓡 n) (𝓡 m) e x.val
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x z) := by
    have h₁ := mfderiv_comp x
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) (E x))
      (E.contMDiff.mdifferentiable (by simp) x)
    have h₂ := mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) x.val)
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x)
    have he : (Subtype.val : V → N) ∘ (E : U → V) =
        (e : M → N) ∘ (Subtype.val : U → M) := rfl
    rw [he, h₂] at h₁
    exact (congrArg (fun A => A z) h₁).symm
  change h.inner (e x.val)
      (mfderiv (𝓡 m) (𝓡 m) (Subtype.val : V → N) (E x)
        (mfderiv (𝓡 n) (𝓡 m) E x v))
      (mfderiv (𝓡 m) (𝓡 m) (Subtype.val : V → N) (E x)
        (mfderiv (𝓡 n) (𝓡 m) E x w)) =
    a * g.inner x.val
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w)
  rw [hchain, hchain]
  exact hinner x.val _ _


theorem connectedComponentMetric_edist_diffeomorph
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 m⟯ N) {a : ℝ} (ha : 0 < a)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 m) e x v)
        (mfderiv (𝓡 n) (𝓡 m) e x w) = a * g.inner x v w)
    (p : M)
    (x y : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
    (h.connectedComponentMetric (e p)).edist
        (Poincare.connectedComponentDiffeomorph e p x)
        (Poincare.connectedComponentDiffeomorph e p y) =
      ENNReal.ofReal (Real.sqrt a) * (g.connectedComponentMetric p).edist x y := by
  let E := Poincare.connectedComponentDiffeomorph e p
  have hm := connectedComponentMetric_inner_diffeomorph g h e hinner p
  calc
    _ = (PoincareConjecture.rescaledMetric (g.connectedComponentMetric p) a ha).edist x y :=
      edist_eq_of_diffeomorph_metric_pullback _ _ E (fun z v w => by
        rw [PoincareConjecture.rescaledMetric_inner]
        exact (hm z v w).symm) x y
    _ = _ := PoincareConjecture.rescaledMetric_edist _ a ha x y

end PoincareConjecture.RiemannianMetric
