import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Extrema
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Analysis.Calculus.DerivativeTest











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Set

noncomputable section

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem horizon_hessian_nonneg_of_isLocalMin
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmin : IsLocalMin f q) (v : TangentSpace (𝓡 n) q) :
    0 ≤ D.hessian f q v v := by
  have h := hessian_nonpos_of_isLocalMax D (f := fun x => -f x)
    (hf.neg) (q := q) hmin.neg v
  have hneg : D.hessian (fun x => -f x) q v v = -D.hessian f q v v := by
    unfold LeviCivitaData.hessian LeviCivitaData.hessianOnFields
    change
      (mvfderiv (𝓡 n) (fun x => mvfderiv (𝓡 n) (fun z => -f z) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) q)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q) -
        (mvfderiv (𝓡 n) (fun z => -f z) q)
          (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) q
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q)) = _
    have hfun : (fun z => -f z) = -f := by
      funext z
      simp
    rw [hfun]
    have hinner :
        (fun x => mvfderiv (𝓡 n) (-f) x
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) =
          (fun x => -mvfderiv (𝓡 n) f x
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) := by
      funext x
      rw [mvfderiv_neg]
      simp
    have houter :
        (fun x => -mvfderiv (𝓡 n) f x
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) =
          -(fun x => mvfderiv (𝓡 n) f x
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) := by
      funext x
      rfl
    rw [hinner, mvfderiv_neg]
    rw [houter, mvfderiv_neg]
    change
      -(mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) q
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q)) -
        (-(mvfderiv (𝓡 n) f q
          (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) q
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q)))) = _
    ring
  rw [hneg] at h
  linarith

theorem horizon_laplacian_nonneg_of_isLocalMin
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmin : IsLocalMin f q) : 0 ≤ D.laplacian f q := by
  unfold laplacian
  exact Finset.sum_nonneg fun i _ => D.horizon_hessian_nonneg_of_isLocalMin hf hmin _

end PoincareConjecture.LeviCivitaData
