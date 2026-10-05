import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.HomotheticField
import PoincareLib.Geometry.Riemannian.Curvature.Derivative
import PoincareLib.Geometry.Riemannian.Curvature.Scalar.Trace
import PoincareLib.Geometry.Riemannian.Tensor.DerivativeOnFields

/-!
# Curvature Laplacian in a homothetic null direction

Differentiating the curvature nullity of a homothetic field twice gives the
radial Laplacian identity used in Kleiner--Lott (corrected 2013), Theorem 41.2,
Case 1, equation (41.9), printed pp. 2675--2676. The computation uses the
actual covariant tensor derivative and the field identity `nabla_X V = c X`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Differentiating the last null curvature slot of a homothetic field. -/
theorem covariantTensorDerivative_riemannEvaluation_homothetic_last
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (u a b w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, w, V x] =
      -D.curvatureTensor x a b w (c • u) := by
  let X := fun z : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  have hs (z : TangentSpace (𝓡 n) x) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (X z)) x :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) z
  have hv := hVsmooth.mdifferentiable (by simp) x
  have h := D.covariantTensorDerivative_on_fields hD.1 ![X a, X b, X w, V] x
    (by intro i; fin_cases i <;> first | exact hs _ | exact hv) u
  have heval (y : M) : (fun i : Fin 4 => (![X a, X b, X w, V] i) y) =
      ![X a y, X b y, X w y, V y] := by
    ext i
    fin_cases i <;> rfl
  simp only [heval] at h
  have hzero (y : M) (a b w : TangentSpace (𝓡 n) y) :=
    D.curvatureTensor_eq_zero_of_constant_covariantDerivative hD V hVsmooth c hV y a b w
  simpa [X, riemannEvaluation, Fin.sum_univ_succ, hzero, hV, mvfderiv_const] using h

/-- The corresponding first-slot identity follows from the curvature symmetries. -/
theorem covariantTensorDerivative_riemannEvaluation_homothetic_first
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (u a b w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, V x, a, b, w] =
      -D.curvatureTensor x (c • u) a b w := by
  rw [D.covariantTensorDerivative_riemannEvaluation_pair_swap hD,
    D.covariantTensorDerivative_riemannEvaluation_skew_last hD,
    D.covariantTensorDerivative_riemannEvaluation_homothetic_last hD V hVsmooth c hV,
    neg_neg, (hD.2.2.2.1 x b w a (c • u)).2.1,
    D.curvatureTensor_swap_first]

/-- The third-slot form is convenient for differentiating a radial plane. -/
theorem covariantTensorDerivative_riemannEvaluation_homothetic_third
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (u a b w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, V x, w] =
      -D.curvatureTensor x a b (c • u) w := by
  rw [D.covariantTensorDerivative_riemannEvaluation_pair_swap hD,
    D.covariantTensorDerivative_riemannEvaluation_homothetic_first hD V hVsmooth c hV,
    (hD.2.2.2.1 x (c • u) w a b).2.1]

/-- One covariant derivative still vanishes when both curvature pairs contain
the homothetic field. -/
theorem covariantTensorDerivative_riemannEvaluation_homothetic_pair_eq_zero
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (u a b : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, V x, a, V x, b] = 0 := by
  rw [D.covariantTensorDerivative_riemannEvaluation_homothetic_first hD V hVsmooth c hV,
    (hD.2.2.2.1 x (c • u) a (V x) b).1,
    D.curvatureTensor_eq_zero_of_constant_covariantDerivative hD V hVsmooth c hV]
  simp

/-- The second covariant derivative on a homothetic radial plane is twice
the curvature of the differentiated radial vector. -/
theorem secondCovariantTensorDerivative_riemannEvaluation_homothetic_pair
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (u w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative D.riemannEvaluation)
      x ![u, u, V x, w, V x, w] = 2 * c ^ 2 * D.curvatureTensor x u w u w := by
  let X := fun z : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  have hs (z : TangentSpace (𝓡 n) x) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (X z)) x :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) z
  have hv := hVsmooth.mdifferentiable (by simp) x
  have h := D.covariantTensorDerivative_on_fields (hD.2.2.1 4 _ hD.1)
    ![X u, V, X w, V, X w] x
    (by intro i; fin_cases i <;> first | exact hs _ | exact hv) u
  have heval (y : M) : (fun i : Fin 5 => (![X u, V, X w, V, X w] i) y) =
      ![X u y, V y, X w y, V y, X w y] := by
    ext i
    fin_cases i <;> rfl
  simp only [heval] at h
  have hzero (y : M) (u a b : TangentSpace (𝓡 n) y) :=
    D.covariantTensorDerivative_riemannEvaluation_homothetic_pair_eq_zero
      hD V hVsmooth c hV y u a b
  simp only [Matrix.vecCons, X, FiberBundle.extend_apply_self,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero,
    ← Fin.cons_update, hV] at h
  simp only [← Matrix.vecCons.eq_def] at h
  simp only [hzero, mvfderiv_const, zero_apply, Finset.univ_eq_empty, Finset.sum_empty,
    D.covariantTensorDerivative_riemannEvaluation_homothetic_first hD V hVsmooth c hV,
    D.covariantTensorDerivative_riemannEvaluation_homothetic_third hD V hVsmooth c hV,
    D.curvatureTensor_smul_first, D.curvatureTensor_smul_third] at h
  rw [h]
  ring

/-- The radial tensor Laplacian is twice the homothety factor squared times
Ricci curvature. This is the invariant form of the cone computation. -/
theorem tensorLaplacian_riemannEvaluation_homothetic_pair
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V)) (c : ℝ)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection V x v = c • v)
    (x : M) (w : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.riemannEvaluation x ![V x, w, V x, w] =
      2 * c ^ 2 * D.ricci x w w := by
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative, Matrix.Fin.cons_vecCons,
    D.secondCovariantTensorDerivative_riemannEvaluation_homothetic_pair hD V hVsmooth c hV,
    D.curvatureTensor_diagonal_pair_swap x _ w, ricci, Finset.mul_sum]

end PoincareMT.LeviCivitaData
