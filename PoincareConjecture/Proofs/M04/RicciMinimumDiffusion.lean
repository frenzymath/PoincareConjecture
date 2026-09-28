import PoincareConjecture.Proofs.M04.TensorNullMinimum
import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M04.CurvatureSymmetries








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricci_tensorLaplacian_nonneg_at_rayleigh_min
    (D : LeviCivitaData g) (m : ℝ)
    (hmin : ∀ (y : M) (v : TangentSpace (𝓡 n) y),
      m * g.inner y v v ≤ D.ricci y v v)
    (x : M) (u : TangentSpace (𝓡 n) x)
    (hnull : D.ricci x u u = m * g.inner x u u) :
    0 ≤ D.tensorLaplacian D.ricciEvaluation x ![u, u] := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let G : CovariantTensorEvaluation n M 2 := fun y v ↦ g.inner y (v 0) (v 1)
  have hG : IsSmoothCovariantTensor G := by
    constructor
    · intro y
      refine ⟨MultilinearMap.mk' (R := ℝ) (G y) ?_ ?_, fun _ ↦ rfl⟩
      · intro v i a b
        fin_cases i <;> simp [G, Function.update, map_add, add_apply]
      · intro v i s a
        fin_cases i <;> simp [G, Function.update, map_smul, smul_apply]
    · intro U hU X hX
      exact (hX 0).inner_bundle (hX 1)
  have hR : IsSmoothCovariantTensor D.ricciEvaluation := isSmoothCovariantTensor_ricciEvaluation D
  let S : CovariantTensorEvaluation n M 2 := fun y v ↦ D.ricciEvaluation y v - m * G y v
  have hS : IsSmoothCovariantTensor S := by
    constructor
    · intro y
      obtain ⟨A, hA⟩ := hR.1 y
      obtain ⟨B, hB⟩ := hG.1 y
      refine ⟨A - m • B, ?_⟩
      intro v
      simp only [S, hA, hB, sub_apply, smul_apply, smul_eq_mul]
    · intro U hU X hX
      exact (hR.2 U hU X hX).sub (contMDiffOn_const.mul (hG.2 U hU X hX))
  have hfirst : D.covariantTensorDerivative S = D.covariantTensorDerivative D.ricciEvaluation := by
    have hthree (y : M) (a b c : TangentSpace (𝓡 n) y) :
        D.covariantTensorDerivative S y ![a, b, c] =
          D.covariantTensorDerivative D.ricciEvaluation y ![a, b, c] := by
      let E := EuclideanSpace ℝ (Fin n)
      let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) y
      have hy : y ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
      let X := FiberBundle.extend E b
      let Y := FiberBundle.extend E c
      have hX := (contMDiffOn_extend_baseSet b).contMDiffAt (e.open_baseSet.mem_nhds hy)
      have hY := (contMDiffOn_extend_baseSet c).contMDiffAt (e.open_baseSet.mem_nhds hy)
      let f := fun z ↦ D.ricci z (X z) (Y z)
      let k := fun z ↦ g.inner z (X z) (Y z)
      have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y :=
        ((contMDiffOn_ricci D e.open_baseSet (contMDiffOn_extend_baseSet b)
          (contMDiffOn_extend_baseSet c)).contMDiffAt
            (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
      have hk : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) k y :=
        (hX.inner_bundle hY).mdifferentiableAt (by simp)
      have hmk : mvfderiv (𝓡 n) (fun z ↦ m * k z) y = m • mvfderiv (𝓡 n) k y := by
        rw [mvfderiv_fun_mul mdifferentiableAt_const hk]
        simp only [mvfderiv_const, smul_zero, add_zero]
      have hsub : mvfderiv (𝓡 n) (fun z ↦ f z - m * k z) y =
          mvfderiv (𝓡 n) f y - m • mvfderiv (𝓡 n) k y := by
        have he := mvfderiv_fun_sub hf ((mdifferentiableAt_const (c := m)).mul hk)
        simpa only [Pi.mul_def, hmk] using! he
      have hmetric : mvfderiv (𝓡 n) k y a =
          g.inner y (D.connection X y a) c + g.inner y b (D.connection Y y a) := by
        simpa only [FiberBundle.extend_apply_self] using!
          metric_derivative_pairing D (FiberBundle.extend E a)
            (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
      have hDS : D.covariantTensorDerivative S y ![a, b, c] =
          mvfderiv (𝓡 n) (fun z ↦ f z - m * k z) y a -
            ((D.ricci y (D.connection X y a) c - m * g.inner y (D.connection X y a) c) +
              (D.ricci y b (D.connection Y y a) - m * g.inner y b (D.connection Y y a))) := by
        simp [LeviCivitaData.covariantTensorDerivative, S, G, LeviCivitaData.ricciEvaluation,
          Fin.sum_univ_succ, Function.update, f, k, X, Y, E]
        ring
      have hDR : D.covariantTensorDerivative D.ricciEvaluation y ![a, b, c] =
          mvfderiv (𝓡 n) f y a -
            (D.ricci y (D.connection X y a) c + D.ricci y b (D.connection Y y a)) := by
        simp [LeviCivitaData.covariantTensorDerivative, LeviCivitaData.ricciEvaluation,
          Fin.sum_univ_succ, Function.update, f, X, Y, E]
      rw [hDS, hDR, hsub]
      simp only [sub_apply, smul_apply, smul_eq_mul, hmetric]
      ring
    funext y v
    have hv : v = ![v 0, v 1, v 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact hthree y _ _ _
  have hsecond : D.iteratedCovariantTensorDerivative S 2 =
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 := by
    simp only [LeviCivitaData.iteratedCovariantTensorDerivative, hfirst]
  have hLap : D.tensorLaplacian S = D.tensorLaplacian D.ricciEvaluation := by
    funext y v
    simp only [LeviCivitaData.tensorLaplacian, hsecond]
  have hsymm (y : M) (a b : TangentSpace (𝓡 n) y) : S y ![a, b] = S y ![b, a] := by
    change D.ricci y a b - m * g.inner y a b = D.ricci y b a - m * g.inner y b a
    rw [ricci_symm D y a b, g.symm y a b]
  rw [← hLap]
  apply tensorLaplacian_nonneg_at_null D hS hsymm isOpen_univ (mem_univ x)
    (fun y _ a ↦ sub_nonneg.mpr (hmin y a)) u
  exact sub_eq_zero.mpr hnull

end PoincareConjecture.M04

