import PoincareConjecture.Proofs.M09.RicciContractions
import PoincareConjecture.Proofs.M09.HessianTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators RealInnerProductSpace

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def pointwiseSecondVariationDensity {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (s : ℝ) (A Y W : TangentSpace (𝓡 n) p) : ℝ :=
  let D := F.connection (T - s ^ 2)
  (F.metric (T - s ^ 2)).inner p W W + D.curvatureTensor p Y A A Y +
    2 * s ^ 2 * D.hessian D.scalarCurvature p Y Y -
    4 * s * ricciDerivativePairing D p Y A Y +
    2 * s * ricciDerivativePairing D p A Y Y

theorem secondVariationIndexDensity_eq_pointwise {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : LVariation F T a b p) (D : LVariationDerivativeData V) (s : ℝ) :
    secondVariationIndexDensity V D s =
      pointwiseSecondVariationDensity F T (V.baseSquareCurve s) s
        (curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval a b) s)
        (squareVariationField V s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
          (squareVariationField V) (sqrtParameterInterval a b) D.variation_extension s) := rfl

theorem curvature_index_smul {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (p : M)
    (A v : TangentSpace (𝓡 n) p) (f : ℝ) :
    D.curvatureTensor p (f • v) A A (f • v) =
      f ^ 2 * D.curvatureTensor p v A A v := by
  let B := curvatureSliceBilinear D (hM04.tensor_calculus n M g D).1 p A A
  have hB (w z : TangentSpace (𝓡 n) p) : B w z = D.curvatureTensor p A w A z :=
    curvatureSliceBilinear_apply D _ p A A w z
  rw [curvatureTensor_first_antisymm hM04 D p (f • v) A A (f • v),
    curvatureTensor_first_antisymm hM04 D p v A A v, ← hB, ← hB]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem ricciDerivative_smul_first_third {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (p : M)
    (A v : TangentSpace (𝓡 n) p) (f : ℝ) :
    ricciDerivativePairing D p (f • v) A (f • v) =
      f ^ 2 * ricciDerivativePairing D p v A v := by
  have hRic := (hM04.tensor_calculus n M g D).2.1
  have hD := (hM04.tensor_calculus n M g D).2.2.1 2 D.ricciEvaluation hRic
  let B := (hD.1 p).choose
  have heq : (fun i : Fin 3 ↦ ![f, 1, f] i • ![v, A, v] i) = ![f • v, A, f • v] := by
    funext i
    fin_cases i <;> simp
  have h := B.map_smul_univ ![f, 1, f] ![v, A, v]
  rw [heq] at h
  change B ![f • v, A, f • v] = _ at h
  rw [← (hD.1 p).choose_spec, ← (hD.1 p).choose_spec] at h
  simpa only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, one_mul, smul_eq_mul, pow_two, ricciDerivativePairing] using h

theorem ricciDerivative_smul_last_two {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (p : M)
    (A v : TangentSpace (𝓡 n) p) (f : ℝ) :
    ricciDerivativePairing D p A (f • v) (f • v) =
      f ^ 2 * ricciDerivativePairing D p A v v := by
  have hRic := (hM04.tensor_calculus n M g D).2.1
  have hD := (hM04.tensor_calculus n M g D).2.2.1 2 D.ricciEvaluation hRic
  let B := (hD.1 p).choose
  have heq : (fun i : Fin 3 ↦ ![1, f, f] i • ![A, v, v] i) = ![A, f • v, f • v] := by
    funext i
    fin_cases i <;> simp
  have h := B.map_smul_univ ![1, f, f] ![A, v, v]
  rw [heq] at h
  change B ![A, f • v, f • v] = _ at h
  rw [← (hD.1 p).choose_spec, ← (hD.1 p).choose_spec] at h
  simpa only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, one_mul, smul_eq_mul, pow_two, ricciDerivativePairing] using h

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem pointwiseSecondVariationDensity_adapted_trace {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (A : TangentSpace (𝓡 n) p) (f fp : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
    ∀ e : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) p),
      (∑ i, pointwiseSecondVariationDensity F T p s A (f • e i)
        (fp • e i - (2 * s * f) • ricciOperator hM04 (F.connection (T - s ^ 2)) p (e i))) =
        (n : ℝ) * fp ^ 2 - 4 * s * f * fp * (F.connection (T - s ^ 2)).scalarCurvature p +
          f ^ 2 * (4 * s ^ 2 * (F.connection (T - s ^ 2)).ricciNormSq p +
            2 * s ^ 2 * (F.connection (T - s ^ 2)).laplacian
              (F.connection (T - s ^ 2)).scalarCurvature p -
            (F.connection (T - s ^ 2)).ricci p A A) := by
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro e
  let L := ricciOperator hM04 D p
  have hf := scalarCurvature_contMDiff hM04 D
  obtain ⟨H, hH⟩ := squareTime_hessian_exists_bilinear F T b hb hwindow p s hs
    D.scalarCurvature hf.contMDiffOn
  have hHscale (v : TangentSpace (𝓡 n) p) :
      D.hessian D.scalarCurvature p (f • v) (f • v) =
        f ^ 2 * D.hessian D.scalarCurvature p v v := by
    rw [hH, hH]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hone (i : Fin n) : g.inner p (e i) (e i) = 1 := by
    change ⟪e i, e i⟫ = (1 : ℝ)
    exact e.inner_eq_one i
  have hnorm (i : Fin n) :
      g.inner p (fp • e i - (2 * s * f) • L (e i))
        (fp • e i - (2 * s * f) • L (e i)) =
      fp ^ 2 - 4 * s * f * fp * D.ricci p (e i) (e i) +
        4 * s ^ 2 * f ^ 2 * g.inner p (L (e i)) (L (e i)) := by
    have hsym : g.inner p (e i) (L (e i)) = g.inner p (L (e i)) (e i) := g.symm p _ _
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul, hone, hsym,
      ricciOperator_pairing, L]
    ring
  have hRic := ricci_orthonormal_trace hM04 D p e
  have hSquare := ricciOperator_orthonormal_square hM04 D p e
  have hR := curvature_orthonormal_index_trace hM04 D p A e
  have hHtrace := squareTime_laplacian_orthonormal_trace F T b hb hwindow p s hs
    D.scalarCurvature hf.contMDiffOn e
  have hDiv := squareTime_covariantRicci_divergence_orthonormal_trace
    F hM04 T b hb hwindow p s hs A e
  have hDir := covariantRicci_direction_orthonormal_trace hM04 D p A e
  change (∑ i, (g.inner p (fp • e i - (2 * s * f) • L (e i))
      (fp • e i - (2 * s * f) • L (e i)) + D.curvatureTensor p (f • e i) A A (f • e i) +
      2 * s ^ 2 * D.hessian D.scalarCurvature p (f • e i) (f • e i) -
      4 * s * ricciDerivativePairing D p (f • e i) A (f • e i) +
      2 * s * ricciDerivativePairing D p A (f • e i) (f • e i))) = _
  simp_rw [hnorm, curvature_index_smul hM04 D, hHscale,
    ricciDerivative_smul_first_third hM04 D, ricciDerivative_smul_last_two hM04 D]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hRic, hSquare, hR, hHtrace, hDiv, hDir]
  ring

end PoincareConjecture.Proofs.M09
