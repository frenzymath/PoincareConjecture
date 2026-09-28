import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Derivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MetricTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private def bilinearOfFourTensor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (a c : E) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ := by
  have hu1 (q r s : E) : Function.update ![a, q, c, r] 1 s = ![a, s, c, r] := by
    ext i; fin_cases i <;> simp
  have hu3 (q r s : E) : Function.update ![a, q, c, r] 3 s = ![a, q, c, s] := by
    ext i; fin_cases i <;> simp
  exact LinearMap.mk₂ ℝ (fun q r ↦ A ![a, q, c, r])
    (fun q q' r ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu1] using
        (A.toLinearMap ![a, q, c, r] 1).map_add q q')
    (fun z q r ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu1] using
        (A.toLinearMap ![a, q, c, r] 1).map_smul z q)
    (fun q r r' ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu3] using
        (A.toLinearMap ![a, q, c, r] 3).map_add r r')
    (fun z q r ↦ by
      simpa only [MultilinearMap.toLinearMap_apply, hu3] using
        (A.toLinearMap ![a, q, c, r] 3).map_smul z r)

@[simp] private lemma bilinearOfFourTensor_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (a c q r : E) :
    bilinearOfFourTensor A a c q r = A ![a, q, c, r] := rfl

lemma covariantTensorDerivative_ricciEvaluation_eq_sum_riemann
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u a c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.ricciEvaluation x ![u, a, c] =
      ∑ p, D.covariantTensorDerivative D.riemannEvaluation x
        ![u, a, g.orthonormalBasis x p, c, g.orthonormalBasis x p] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let X := fun z : TangentSpace (𝓡 n) x ↦
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  let T : CovariantTensorEvaluation n M 2 := fun y w ↦
    D.curvatureTensor y (X a y) (w 0) (X c y) (w 1)
  have hlin : ∀ᶠ y in 𝓝 x, ∃ A : TangentSpace (𝓡 n) y →ₗ[ℝ]
      TangentSpace (𝓡 n) y →ₗ[ℝ] ℝ, ∀ q r, T y ![q, r] = A q r := by
    filter_upwards [] with y
    obtain ⟨A, hA⟩ := hD.1.1 y
    refine ⟨bilinearOfFourTensor A (X a y) (X c y), ?_⟩
    intro q r
    exact hA ![X a y, q, X c y, r]
  have hT (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
        (fun y ↦ T y ![X (b i) y, X (b j) y]) x := by
    convert (hD.1.contMDiffAt_extend x
      ![a, b i, c, b j]).mdifferentiableAt (by simp) using 1
    ext y
    rfl
  have htrace := mvfderiv_metricTrace_eq_fixed_trace_sub_gram
    (g := g) T x hlin hT u
  dsimp [T] at htrace
  have htrace' : mvfderiv (𝓡 n)
      (fun y ↦ ∑ i, D.curvatureTensor y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a y)
        (g.orthonormalBasis y i)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) c y)
        (g.orthonormalBasis y i)) x u =
      mvfderiv (𝓡 n)
        (fun y ↦ ∑ i, D.curvatureTensor y (X a y)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y)
          (X c y) (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y)) x u -
        ∑ i, ∑ j, mvfderiv (𝓡 n)
          (fun y ↦ g.inner y
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y)
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b j) y)) x u *
          D.curvatureTensor x (X a x) (b i) (X c x) (b j) := by
    simpa [X, b] using htrace
  have hleft : D.covariantTensorDerivative D.ricciEvaluation x ![u, a, c] =
      mvfderiv (𝓡 n) (fun y ↦ D.ricci y (X a y) (X c y)) x u -
        (D.ricci x (D.connection (X a) x u) c +
          D.ricci x a (D.connection (X c) x u)) := by
    simp [covariantTensorDerivative, ricciEvaluation, X]
  have hricci : (fun y ↦ D.ricci y (X a y) (X c y)) =
      (fun y ↦ ∑ i, D.curvatureTensor y (X a y)
        (g.orthonormalBasis y i) (X c y) (g.orthonormalBasis y i)) := by
    funext y
    rfl
  have hleft' : D.covariantTensorDerivative D.ricciEvaluation x ![u, a, c] =
      mvfderiv (𝓡 n) (fun y ↦ ∑ i, D.curvatureTensor y (X a y)
        (g.orthonormalBasis y i) (X c y) (g.orthonormalBasis y i)) x u -
        (D.ricci x (D.connection (X a) x u) c +
          D.ricci x a (D.connection (X c) x u)) := by
    rw [hleft, hricci]
  have hp (p : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.covariantTensorDerivative D.riemannEvaluation x
          ![u, a, b p, c, b p] =
        mvfderiv (𝓡 n) (fun y ↦ D.curvatureTensor y
          (X a y) (X (b p) y) (X c y) (X (b p) y)) x u -
          (D.curvatureTensor x (D.connection (X a) x u) (b p) c (b p) +
           D.curvatureTensor x a (D.connection (X (b p)) x u) c (b p) +
           D.curvatureTensor x a (b p) (D.connection (X c) x u) (b p) +
           D.curvatureTensor x a (b p) c (D.connection (X (b p)) x u)) := by
    simpa [X] using D.covariantTensorDerivative_riemannEvaluation_eq x u a (b p) c (b p)
  have hmetric (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      mvfderiv (𝓡 n) (fun y ↦ g.inner y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b j) y)) x u =
        inner ℝ (D.connection (X (b i)) x u) (b j) +
          inner ℝ (b i) (D.connection (X (b j)) x u) := by
    exact D.mvfderiv_metric_extend x u (b i) (b j)
  obtain ⟨AR, hAR⟩ := hD.1.1 x
  have hcorr := bilinear_sum_frame_corrections
    (bilinearOfFourTensor AR a c) b (fun i ↦ D.connection (X (b i)) x u)
  simp only [bilinearOfFourTensor_apply, ← hAR] at hcorr
  simp [riemannEvaluation] at hcorr
  have hsum := mvfderiv_sum_apply
    (fun p y ↦ D.curvatureTensor y (X a y) (X (b p) y) (X c y) (X (b p) y))
    x u (fun p ↦ hT p p)
  have hright := congrArg (fun f : _ → ℝ => ∑ p, f p) (funext fun p ↦ hp p)
  rw [hleft', hright, htrace']
  simp only [X, FiberBundle.extend_apply_self] at hmetric hcorr hsum ⊢
  simp_rw [hmetric]
  rw [← hcorr, hsum]
  simp only [ricci, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring!

end PoincareConjecture.LeviCivitaData
