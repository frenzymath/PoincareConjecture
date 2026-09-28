import PoincareConjecture.Proofs.M04.SectionalMinimumDiffusion









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in


theorem sectional_laplacian_nonneg_of_local_lower
    (D : LeviCivitaData g) (m : ℝ) {U : Set M} (hU : IsOpen U)
    (hmin : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      m * metricGram g y a b ≤ D.curvatureTensor y a b a b)
    (x : M) (hx : x ∈ U) (u v : TangentSpace (𝓡 n) x)
    (hnull : D.curvatureTensor x u v u v = m * metricGram g x u v) :
    0 ≤ D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] := by
  classical
  let G := metricGramEvaluation g
  have hG : IsSmoothCovariantTensor G := isSmoothCovariantTensor_metricGramEvaluation g
  have hR : IsSmoothCovariantTensor D.riemannEvaluation :=
    isSmoothCovariantTensor_riemannEvaluation D
  let S : CovariantTensorEvaluation n M 4 := fun y w => D.riemannEvaluation y w - m * G y w
  have hS : IsSmoothCovariantTensor S := by
    constructor
    · intro y
      obtain ⟨A, hA⟩ := hR.1 y
      obtain ⟨B, hB⟩ := hG.1 y
      refine ⟨A - m • B, ?_⟩
      intro w
      simp only [S, hA, hB, sub_apply, smul_apply, smul_eq_mul]
    · intro W hW X hX
      exact (hR.2 W hW X hX).sub (contMDiffOn_const.mul (hG.2 W hW X hX))
  have hline (y : M) (w : Fin 5 → TangentSpace (𝓡 n) y) :
      D.covariantTensorDerivative S y w =
        D.covariantTensorDerivative D.riemannEvaluation y w -
          m * D.covariantTensorDerivative G y w := by
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) y
    have hy : y ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
    let X : Fin 4 → (z : M) → TangentSpace (𝓡 n) z :=
      fun i => FiberBundle.extend E (w i.succ)
    have hX (i : Fin 4) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (T% (X i)) e.baseSet := contMDiffOn_extend_baseSet (w i.succ)
    let f : M → ℝ := fun z => D.riemannEvaluation z (fun i => X i z)
    let k : M → ℝ := fun z => G z (fun i => X i z)
    have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y :=
      ((hR.2 e.baseSet e.open_baseSet X hX).contMDiffAt
        (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
    have hk : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) k y :=
      ((hG.2 e.baseSet e.open_baseSet X hX).contMDiffAt
        (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
    have hmk : mvfderiv (𝓡 n) (fun z => m * k z) y = m • mvfderiv (𝓡 n) k y := by
      rw [mvfderiv_fun_mul mdifferentiableAt_const hk]
      simp only [mvfderiv_const, smul_zero, add_zero]
    have hsub : mvfderiv (𝓡 n) (fun z => f z - m * k z) y =
        mvfderiv (𝓡 n) f y - m • mvfderiv (𝓡 n) k y := by
      have h := mvfderiv_fun_sub hf ((mdifferentiableAt_const (c := m)).mul hk)
      simpa only [Pi.mul_def, hmk] using! h
    let C (i : Fin 4) := Function.update (fun j => w j.succ) i (D.connection (X i) y (w 0))
    change mvfderiv (𝓡 n) (fun z => f z - m * k z) y (w 0) -
        (∑ i, (D.riemannEvaluation y (C i) - m * G y (C i))) =
      (mvfderiv (𝓡 n) f y (w 0) - ∑ i, D.riemannEvaluation y (C i)) -
        m * (mvfderiv (𝓡 n) k y (w 0) - ∑ i, G y (C i))
    rw [hsub]
    simp only [sub_apply, smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hfirst : D.covariantTensorDerivative S =
      D.covariantTensorDerivative D.riemannEvaluation := by
    funext y w
    have hz : D.covariantTensorDerivative G y w = 0 :=
      congrFun (congrFun (covariantTensorDerivative_metricGramEvaluation D) y) w
    simpa only [hz, mul_zero, sub_zero] using hline y w
  have hsecond : D.iteratedCovariantTensorDerivative S 2 =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 := by
    simp only [LeviCivitaData.iteratedCovariantTensorDerivative, hfirst]
  have hLap : D.tensorLaplacian S = D.tensorLaplacian D.riemannEvaluation := by
    funext y w
    simp only [LeviCivitaData.tensorLaplacian, hsecond]
  have hpair (a b c d : TangentSpace (𝓡 n) x) :
      S x ![a, b, c, d] = S x ![c, d, a, b] := by
    change D.curvatureTensor x a b c d - m *
        (g.inner x a c * g.inner x b d - g.inner x a d * g.inner x b c) =
      D.curvatureTensor x c d a b - m *
        (g.inner x c a * g.inner x d b - g.inner x c b * g.inner x d a)
    rw [curvatureTensor_pair_exchange D x a b c d,
      g.symm x c a, g.symm x d b, g.symm x c b, g.symm x d a]
    ring
  have hdiag (y : M) (a b : TangentSpace (𝓡 n) y) :
      S y ![a, b, a, b] = D.curvatureTensor y a b a b - m * metricGram g y a b := by
    change D.curvatureTensor y a b a b - m *
        (g.inner y a a * g.inner y b b - g.inner y a b * g.inner y b a) = _
    rw [g.symm y b a]
    simp only [metricGram, pow_two]
  rw [← hLap]
  apply tensorLaplacian_nonneg_at_sectional_null D hS hU hx hpair
    (fun y hy a b => by rw [hdiag]; exact sub_nonneg.mpr (hmin y hy a b)) u v
  rw [hdiag]
  exact sub_eq_zero.mpr hnull

end PoincareConjecture.Proofs.M46
