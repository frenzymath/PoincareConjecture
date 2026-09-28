import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureOnFields_eq_zero_of_constant_covariantDerivative
    (D : LeviCivitaData g) (V : (x : M) → TangentSpace (𝓡 n) x) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (X Y : (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x) :
    D.curvatureOnFields X Y V x = 0 := by
  have hXY (Z : (y : M) → TangentSpace (𝓡 n) y) :
      (fun y => D.connection V y (Z y)) = c • Z := funext fun y => hV y (Z y)
  rw [curvatureOnFields, hXY, hXY,
    D.connection.isCovariantDerivativeOn.smul_const c hY,
    D.connection.isCovariantDerivativeOn.smul_const c hX, hV]
  simp only [smul_apply]
  rw [← smul_sub, D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hX hY,
    sub_self]

theorem curvature_eq_zero_of_constant_covariantDerivative
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.curvature x u v (V x) = 0 := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨U, hU, hX⟩ := FiberBundle.exists_contMDiffOn_extend
    (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) u
  obtain ⟨W, hW, hY⟩ := FiberBundle.exists_contMDiffOn_extend
    (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) v
  obtain ⟨S, hSsub, hSopen, hxS⟩ := mem_nhds_iff.mp (inter_mem hU hW)
  have hcurv := hD.2.2.2.2 S hSopen X Y V
    (hX.mono (hSsub.trans inter_subset_left))
    (hY.mono (hSsub.trans inter_subset_right)) hVsmooth.contMDiffOn x hxS
  have hzero := D.curvatureOnFields_eq_zero_of_constant_covariantDerivative V c hV X Y x
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
  simpa only [X, Y, FiberBundle.extend_apply_self] using hcurv.symm.trans hzero

theorem curvatureTensor_eq_zero_of_constant_covariantDerivative
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w (V x) = 0 := by
  rw [curvatureTensor, D.curvature_eq_zero_of_constant_covariantDerivative hD V hVsmooth c hV]
  simp

end PoincareConjecture.LeviCivitaData
