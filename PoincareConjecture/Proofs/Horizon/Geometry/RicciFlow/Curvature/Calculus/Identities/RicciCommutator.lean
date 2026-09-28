import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.TensorCommutator
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction
import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter Function

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricci_second_derivative_commutator_trace (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    2 * (∑ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      (D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
          ![u, g.orthonormalBasis x i, g.orthonormalBasis x i, v] -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
          ![g.orthonormalBasis x i, u, g.orthonormalBasis x i, v])) =
      D.ricciReaction x u v := by
  classical
  let b := g.orthonormalBasis x
  let E := TangentSpace (𝓡 n) x
  let H := D.iteratedCovariantTensorDerivative D.ricciEvaluation 2
  let R := D.ricci
  let K := D.curvature
  let A := D.ricciEvaluation
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hA := (isSmoothCovariantTensor_ricciEvaluation D).1 x
  obtain ⟨P, hP⟩ := hA
  have hR (a c : E) : R x a c = P ![a, c] := by
    exact hP ![a, c]
  have hR_add_left (a a' c : E) : R x (a + a') c = R x a c + R x a' c := by
    rw [hR, hR, hR]
    have h := P.map_update_add ![a, c] 0 a a'
    have hu : Function.update ![a, c] 0 (a + a') = ![a + a', c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hu₁ : Function.update ![a, c] 0 a = ![a, c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hu₂ : Function.update ![a, c] 0 a' = ![a', c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    simpa only [hu, hu₁, hu₂] using h
  have hR_smul_left (r : ℝ) (a c : E) : R x (r • a) c = r * R x a c := by
    rw [hR, hR]
    have h := P.map_update_smul ![a, c] 0 r a
    have hu : Function.update ![a, c] 0 (r • a) = ![r • a, c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hu₁ : Function.update ![a, c] 0 a = ![a, c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    simpa only [hu, hu₁, smul_eq_mul] using h
  have hR_add_right (a c c' : E) : R x a (c + c') = R x a c + R x a c' := by
    rw [hR, hR, hR]
    have h := P.map_update_add ![a, c] 1 c c'
    have hu : Function.update ![a, c] 1 (c + c') = ![a, c + c'] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hu₁ : Function.update ![a, c] 1 c = ![a, c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hu₂ : Function.update ![a, c] 1 c' = ![a, c'] := by
      ext i
      fin_cases i <;> simp [Function.update]
    simpa only [hu, hu₁, hu₂] using h
  have hR_smul_right (r : ℝ) (a c : E) : R x a (r • c) = r * R x a c := by
    rw [hR, hR]
    have h := P.map_update_smul ![a, c] 1 r c
    have hu : Function.update ![a, c] 1 (r • c) = ![a, r • c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hu₁ : Function.update ![a, c] 1 c = ![a, c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    simpa only [hu, hu₁, smul_eq_mul] using h
  have hExpand (a : E) : a = ∑ j, (g.inner x (b j) a) • b j := by
    symm
    exact b.sum_repr' a
  have hRicciExpand (a c : E) :
      R x a c = ∑ j, (g.inner x (b j) a) * R x (b j) c := by
    conv_lhs => rw [hExpand a]
    have hsum (f : Fin (Module.finrank ℝ E) → E) :
        R x (∑ j, f j) c = ∑ j, R x (f j) c := by
      classical
      induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        simpa only [zero_smul, zero_mul] using hR_smul_left 0 (0 : E) c
      | @insert j s hj ih =>
        simp only [Finset.sum_insert hj, hR_add_left, ih]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hR_smul_left]
  have hRicciExpandRight (a c : E) :
      R x a c = ∑ j, (g.inner x (b j) c) * R x a (b j) := by
    conv_lhs => rw [hExpand c]
    have hsum (f : Fin (Module.finrank ℝ E) → E) :
        R x a (∑ j, f j) = ∑ j, R x a (f j) := by
      classical
      induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        simpa only [zero_smul, zero_mul] using hR_smul_right 0 a (0 : E)
      | @insert j s hj ih =>
        simp only [Finset.sum_insert hj, hR_add_right, ih]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hR_smul_right]
  have hcons (a c d f : E) : Fin.cons a (Fin.cons c ![d, f]) = ![a, c, d, f] := by
    ext i
    fin_cases i <;> rfl
  have hComm (i : Fin (Module.finrank ℝ E)) :
      H x ![u, b i, b i, v] - H x ![b i, u, b i, v] =
        -(∑ j, A x (Function.update ![b i, v] j (K x u (b i) (![b i, v] j)))) := by
    have hc := covariantTensorDerivative_commutator D
      (isSmoothCovariantTensor_ricciEvaluation D) x u (b i) ![b i, v]
    simpa only [hcons] using hc
  have hCommSum :
      ∑ i, (H x ![u, b i, b i, v] - H x ![b i, u, b i, v]) =
        -∑ i, (R x (K x u (b i) (b i)) v + R x (b i) (K x u (b i) v)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hComm i]
    rw [Fin.sum_univ_two]
    simp [A, R, LeviCivitaData.ricciEvaluation, Function.update]
  have hFirst :
      ∑ i, R x (K x u (b i) (b i)) v =
        ∑ i, ∑ j, D.curvatureTensor x u (b i) (b j) (b i) * R x (b j) v := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hRicciExpand]
    apply Finset.sum_congr rfl
    intro j hj
    rw [g.symm]
    rfl
  have hSecond :
      ∑ i, R x (b i) (K x u (b i) v) =
        -(∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) * R x (b i) (b j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hRicciExpandRight]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [g.symm]
    change D.curvatureTensor x u (b i) (b j) v * R x (b i) (b j) =
      -(D.curvatureTensor x u (b i) v (b j) * R x (b i) (b j))
    rw [curvatureTensor_swap_last]
    ring
  have hFirstRicci :
      ∑ i, ∑ j, D.curvatureTensor x u (b i) (b j) (b i) * R x (b j) v =
        ∑ i, R x u (b i) * R x (b i) v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_mul]
    congr 1
  have hReaction :
      ∑ i, (H x ![u, b i, b i, v] - H x ![b i, u, b i, v]) =
        (∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) * R x (b i) (b j)) -
          ∑ i, R x u (b i) * R x (b i) v := by
    calc
      _ = -∑ i, (R x (K x u (b i) (b i)) v + R x (b i) (K x u (b i) v)) := hCommSum
      _ = _ := by
        rw [Finset.sum_add_distrib, hFirst, hSecond, hFirstRicci]
        ring
  unfold LeviCivitaData.ricciReaction
  simpa only [H, b, R, K, mul_sub] using congrArg (fun z : ℝ ↦ 2 * z) hReaction

end PoincareConjecture.RicciFlowAnalysis
