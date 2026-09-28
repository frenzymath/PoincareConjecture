import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.SpatialContact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Jets












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Matrix Filter

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



lemma covariantTensorDerivative_eq_mvfderiv_of_zero_jets
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (E : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hE : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (E i)) x)
    (hfirst : ∀ i a, D.connection (E i) x a = 0)
    (a : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative T x (Fin.cons a (fun i => E i x)) =
      mvfderiv (𝓡 n) (fun y => T y (fun i => E i y)) x a := by
  obtain ⟨B, hB⟩ := hT.1 x
  rw [D.covariantTensorDerivative_on_fields hT E x
    (fun i => (hE i).mdifferentiableAt (by simp)) a]
  simp only [hfirst, hB, B.map_update_zero, Finset.sum_const_zero, sub_zero]






theorem tensor_matrix_diffusion_nonneg_at_null [T2Space M]
    {I J : Type} [Fintype I]
    (D : LeviCivitaData g) (k : I → I → ℕ)
    (T : (i j : I) → CovariantTensorEvaluation n M (k i j))
    (hT : ∀ i j, IsSmoothCovariantTensor (T i j))
    (s : (i j : I) → Fin (k i j) → J)
    (x : M) (v : J → TangentSpace (𝓡 n) x)
    (hpos : ∀ᶠ y in 𝓝 x, ∀ e : J → TangentSpace (𝓡 n) y,
      Matrix.PosSemidef (fun i j => T i j y (fun l => e (s i j l))))
    (z : I → ℝ)
    (hnull : z ⬝ᵥ ((fun i j => T i j x (fun l => v (s i j l))) *ᵥ z) = 0)
    (V : I → TangentSpace (𝓡 n) x) :
    0 ≤ (∑ i, ∑ j, z i * D.tensorLaplacian (T i j) x
        (fun l => v (s i j l)) * z j) +
      4 * (∑ i, ∑ j, z i * D.covariantTensorDerivative (T i j) x
          (Fin.cons (V j) (fun l => v (s i j l)))) +
      2 * (∑ i, ∑ j,
        T i j x (fun l => v (s i j l)) * g.inner x (V i) (V j)) := by
  classical
  choose r Y hr hrU hY hinit hparallel hfirst hsecond using
    fun j => D.exists_radialParallelField x (v j)
  let E := fun j => LeviCivitaData.fieldFromCenteredCoordinates x (Y j)
  let A : M → Matrix I I ℝ := fun y i j => T i j y (fun l => E (s i j l) y)
  have hE (j : J) (y : M) (hy : y ∈ (extChartAt (𝓡 n) x).source) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (E j)) y :=
    LeviCivitaData.contMDiffAt_fieldFromCenteredCoordinates x (hY j).contDiffAt hy
  have hA (i j : I) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => A y i j) (extChartAt (𝓡 n) x).source :=
    (hT i j).2 _ (isOpen_extChartAt_source x) _
      (fun l y hy => (hE (s i j l) y hy).contMDiffWithinAt)
  have hpositive : ∀ᶠ y in 𝓝 x, (A y).PosSemidef := by
    filter_upwards [hpos] with y hy
    exact hy (fun j => E j y)
  have hvalue (i j : I) : A x i j = T i j x (fun l => v (s i j l)) := by
    simp only [A, E, hinit]
  have hnullA : z ⬝ᵥ (A x *ᵥ z) = 0 := by
    simpa only [dotProduct, mulVec, hvalue] using hnull
  have hlap (i j : I) : D.laplacian (fun y => A y i j) x =
      D.tensorLaplacian (T i j) x (fun l => v (s i j l)) := by
    have h := D.tensorLaplacian_eq_laplacian_of_zero_jets (hT i j)
      (fun l => E (s i j l)) x
      (fun l => hE (s i j l) x (mem_extChartAt_source x))
      (fun l => hfirst (s i j l)) (fun l => hsecond (s i j l))
    simpa only [E, hinit] using h.symm
  have hder (i j : I) (a : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) (fun y => A y i j) x a =
        D.covariantTensorDerivative (T i j) x
          (Fin.cons a (fun l => v (s i j l))) := by
    have h := covariantTensorDerivative_eq_mvfderiv_of_zero_jets D (hT i j)
      (fun l => E (s i j l)) x
      (fun l => hE (s i j l) x (mem_extChartAt_source x))
      (fun l => hfirst (s i j l)) a
    simpa only [E, hinit] using h.symm
  have h := quadratic_diffusion_nonneg_of_prescribed_gradients D
    (isOpen_extChartAt_source x) hA (mem_extChartAt_source x) hpositive z hnullA V
  have hright (i j : I) :
      g.inner x (V i) (D.gradient (fun y => A y i j) x) =
        D.covariantTensorDerivative (T i j) x
          (Fin.cons (V i) (fun l => v (s i j l))) := by
    rw [g.symm, D.inner_gradient, hder]
  simp only [hlap, D.inner_gradient, hder, hright, hvalue,
    Finset.sum_add_distrib] at h
  have hsym (i j : I) (a : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative (T i j) x
          (Fin.cons a (fun l => v (s i j l))) =
        D.covariantTensorDerivative (T j i) x
          (Fin.cons a (fun l => v (s j i l))) := by
    rw [← hder, ← hder]
    have heq : (fun y => A y i j) =ᶠ[𝓝 x] (fun y => A y j i) := by
      filter_upwards [hpositive] with y hy
      simpa only [star_trivial] using hy.1.apply j i
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  have hswap : (∑ i, ∑ j, z j * D.covariantTensorDerivative (T i j) x
      (Fin.cons (V i) (fun l => v (s i j l)))) =
      ∑ i, ∑ j, z i * D.covariantTensorDerivative (T i j) x
        (Fin.cons (V j) (fun l => v (s i j l))) := by
    rw [Finset.sum_comm]
    simp_rw [hsym]
  rw [hswap] at h
  linarith only [h]

end Poincare.RicciFlow.Harnack
