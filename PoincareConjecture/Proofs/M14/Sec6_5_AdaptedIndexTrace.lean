import PoincareConjecture.Proofs.M14.Mathlib.HessianTrace
import PoincareConjecture.Proofs.M09.AdaptedIndexTrace
import PoincareConjecture.Proofs.M04.SecondBianchi

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem covariantRicci_divergence_orthonormal_trace
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (q : M)
    (A : TangentSpace (𝓡 n) q) {ι : Type*} [Fintype ι] :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) q),
      (∑ i, ricciDerivativePairing D q (e i) A (e i)) =
        mvfderiv (𝓡 n) D.scalarCurvature q A / 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro e
  rw [Proofs.M09.covariantRicci_divergence_trace_basis_eq hM04 D q A e]
  have h := Proofs.M09.scalarCurvature_mvfderiv_of_bianchi hM04 D q
    (M04.riemann_second_bianchi D q) A
  linarith

noncomputable def sliceIndexDensity (D : LeviCivitaData g) (q : M) (s : ℝ)
    (A Y W : TangentSpace (𝓡 n) q) : ℝ :=
  g.inner q W W + D.curvatureTensor q Y A A Y +
    2 * s ^ 2 * D.hessian D.scalarCurvature q Y Y -
    4 * s * ricciDerivativePairing D q Y A Y +
    2 * s * ricciDerivativePairing D q A Y Y

theorem sliceIndexDensity_adapted_trace (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (q : M) (s : ℝ) (A : TangentSpace (𝓡 n) q) (f fp : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) q),
      (∑ i, sliceIndexDensity D q s A (f • e i)
        (fp • e i - (2 * s * f) • Proofs.M09.ricciOperator hM04 D q (e i))) =
      (n : ℝ) * fp ^ 2 - 4 * s * f * fp * D.scalarCurvature q +
        f ^ 2 * (4 * s ^ 2 * D.ricciNormSq q +
          2 * s ^ 2 * D.laplacian D.scalarCurvature q - D.ricci q A A) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro e
  let L := Proofs.M09.ricciOperator hM04 D q
  have hf := Proofs.M09.scalarCurvature_contMDiff hM04 D
  obtain ⟨H, hH⟩ := hessian_exists_bilinear D D.scalarCurvature q (hf q)
  have hHscale (v : TangentSpace (𝓡 n) q) :
      D.hessian D.scalarCurvature q (f • v) (f • v) =
        f ^ 2 * D.hessian D.scalarCurvature q v v := by
    rw [hH, hH]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hone (i : Fin n) : g.inner q (e i) (e i) = 1 := e.inner_eq_one i
  have hnorm (i : Fin n) :
      g.inner q (fp • e i - (2 * s * f) • L (e i))
        (fp • e i - (2 * s * f) • L (e i)) =
      fp ^ 2 - 4 * s * f * fp * D.ricci q (e i) (e i) +
        4 * s ^ 2 * f ^ 2 * g.inner q (L (e i)) (L (e i)) := by
    have hsym : g.inner q (e i) (L (e i)) = g.inner q (L (e i)) (e i) := g.symm q _ _
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul, hone, hsym,
      Proofs.M09.ricciOperator_pairing, L]
    ring
  have hRic := Proofs.M09.ricci_orthonormal_trace hM04 D q e
  have hSquare := Proofs.M09.ricciOperator_orthonormal_square hM04 D q e
  have hR := Proofs.M09.curvature_orthonormal_index_trace hM04 D q A e
  have hHtrace := laplacian_eq_orthonormal_hessian_trace D D.scalarCurvature q (hf q) e
  have hDiv := covariantRicci_divergence_orthonormal_trace hM04 D q A e
  have hDir := Proofs.M09.covariantRicci_direction_orthonormal_trace hM04 D q A e
  unfold sliceIndexDensity
  change (∑ i, (g.inner q (fp • e i - (2 * s * f) • L (e i))
      (fp • e i - (2 * s * f) • L (e i)) + D.curvatureTensor q (f • e i) A A (f • e i) +
      2 * s ^ 2 * D.hessian D.scalarCurvature q (f • e i) (f • e i) -
      4 * s * ricciDerivativePairing D q (f • e i) A (f • e i) +
      2 * s * ricciDerivativePairing D q A (f • e i) (f • e i))) = _
  simp_rw [hnorm, Proofs.M09.curvature_index_smul hM04 D, hHscale,
    Proofs.M09.ricciDerivative_smul_first_third hM04 D,
    Proofs.M09.ricciDerivative_smul_last_two hM04 D]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hRic, hSquare, hR, ← hHtrace, hDiv, hDir]
  ring

theorem sliceIndexDensity_adapted_trace_of_pair (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (q : M) (s : ℝ) (A : TangentSpace (𝓡 n) q) (f fp : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) q))
      (W : Fin n → TangentSpace (𝓡 n) q),
      (∀ i v, g.inner q (W i) v = fp * g.inner q (e i) v -
        2 * s * f * D.ricci q (e i) v) →
      (∑ i, sliceIndexDensity D q s A (f • e i) (W i)) =
      (n : ℝ) * fp ^ 2 - 4 * s * f * fp * D.scalarCurvature q +
        f ^ 2 * (4 * s ^ 2 * D.ricciNormSq q +
          2 * s ^ 2 * D.laplacian D.scalarCurvature q - D.ricci q A A) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro e W hW
  have heq (i : Fin n) :
      W i = fp • e i - (2 * s * f) • Proofs.M09.ricciOperator hM04 D q (e i) := by
    apply ext_inner_right ℝ
    intro v
    change g.inner q (W i) v = _
    simp only [hW, inner_sub_left, real_inner_smul_left]
    exact congrArg (fun r => fp * g.inner q (e i) v - 2 * s * f * r)
      (Proofs.M09.ricciOperator_pairing hM04 D q (e i) v).symm
  simp_rw [heq]
  exact sliceIndexDensity_adapted_trace hM04 D q s A f fp e

end PoincareConjecture.M14
