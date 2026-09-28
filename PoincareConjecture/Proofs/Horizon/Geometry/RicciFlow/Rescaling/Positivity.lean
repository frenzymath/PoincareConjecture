import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Contraction
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.Bounds








set_option autoImplicit false
open scoped Manifold ContDiff Bundle BigOperators
universe u

namespace PoincareConjecture

private theorem sum_four_exchange {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ι → ι → ι → κ → κ → κ → κ → ℝ) :
    (∑ a, ∑ b, ∑ d, ∑ e, ∑ i, ∑ j, ∑ k, ∑ l, f a b d e i j k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ d, ∑ e, f a b d e i j k l := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a : (ι × ι) × (ι × ι) ↦
      fun i : (κ × κ) × (κ × κ) ↦
        f a.1.1 a.1.2 a.2.1 a.2.2 i.1.1 i.1.2 i.2.1 i.2.2))

private theorem sum_fin_cons {ι : Type*} [Fintype ι] {d : ℕ}
    (f : (Fin (d + 1) → ι) → ℝ) :
    (∑ p, f p) = ∑ a, ∑ q, f (Fin.cons a q) := by
  calc
    (∑ p, f p) = ∑ p : ι × (Fin d → ι), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ι)).symm _ _
        (fun p ↦ congrArg f (Fin.cons_self_tail p).symm)
    _ = _ := Fintype.sum_prod_type _

private theorem fourTensor_expand {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] (b : Module.Basis ι ℝ E)
    (R : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (v : Fin 4 → E) :
    R v = ∑ i, ∑ j, ∑ k, ∑ l,
      (b.repr (v 0) i * b.repr (v 1) j * b.repr (v 2) k * b.repr (v 3) l) *
        R ![b i, b j, b k, b l] := by
  classical
  conv_lhs => rw [show v = (fun a ↦ ∑ i, b.repr (v a) i • b i) by
    funext a; exact (b.sum_repr (v a)).symm]
  rw [R.map_sum]
  simp only [R.map_smul_univ, smul_eq_mul, sum_fin_cons, Fin.cons_zero,
    Fintype.sum_unique, Fin.prod_univ_succ, Fin.prod_univ_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fin.cons_succ, mul_one]
  ring_nf
  congr 1
  apply congrArg R
  funext a
  fin_cases a <;> rfl

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem rescaledMetric_nonnegativeCurvatureOperator
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M) (hD : D.NonnegativeCurvatureOperator x) :
    (rescaledMetric_connection g D c hc).NonnegativeCurvatureOperator x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := (g.orthonormalBasis x).toBasis
  let v := (rescaledMetric g c hc).orthonormalBasis x
  let U := fun a i ↦ b.repr (v a) i
  obtain ⟨R, hR⟩ := D.curvatureTensor_multilinear x
  intro A hA
  let B := fun i j ↦ ∑ a, ∑ d, A a d * U a i * U d j
  have hB : LeviCivitaData.IsSkewCoefficient _ B := by
    intro i j
    dsimp only [B]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro a _
    rw [hA d a]
    ring
  have hexpand (a d e f) : D.curvatureTensor x (v a) (v d) (v e) (v f) =
      ∑ i, ∑ j, ∑ k, ∑ l, (U a i * U d j * U e k * U f l) *
        D.curvatureTensor x (b i) (b j) (b k) (b l) := by
    simpa [← hR, LeviCivitaData.riemannEvaluation, U] using
      fourTensor_expand b R ![v a, v d, v e, v f]
  have hquad : (∑ a, ∑ d, ∑ e, ∑ f,
      A a d * A e f * D.curvatureTensor x (v a) (v d) (v e) (v f)) =
      D.curvatureOperatorQuadratic x B := by
    simp only [hexpand, Finset.mul_sum]
    rw [sum_four_exchange]
    unfold LeviCivitaData.curvatureOperatorQuadratic
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    dsimp only [B]
    simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    change _ = A a d * U a i * U d j * (A e f * U e k * U f l) *
      D.curvatureTensor x (b i) (b j) (b k) (b l)
    ring
  change 0 ≤ ∑ a, ∑ d, ∑ e, ∑ f,
    A a d * A e f * (rescaledMetric_connection g D c hc).curvatureTensor
      x (v a) (v d) (v e) (v f)
  simp only [rescaledMetric_curvatureTensor]
  simp_rw [show ∀ a d e f, A a d * A e f *
      (c * D.curvatureTensor x (v a) (v d) (v e) (v f)) =
      c * (A a d * A e f * D.curvatureTensor x (v a) (v d) (v e) (v f)) by
    intros; ring]
  simp_rw [← Finset.mul_sum]
  rw [hquad]
  exact mul_nonneg hc.le (hD B hB)

end PoincareConjecture
