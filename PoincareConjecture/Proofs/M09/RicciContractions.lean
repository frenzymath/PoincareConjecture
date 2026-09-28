import PoincareConjecture.Proofs.M09.BasisContractions
import PoincareConjecture.Proofs.M09.ContractedBianchi








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators RealInnerProductSpace

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def ricciOperator (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) : TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  exact formOperator (tensorBilinear g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 p)

theorem ricciOperator_pairing (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (v w : TangentSpace (𝓡 n) p) :
    g.inner p (ricciOperator hM04 D p v) w = D.ricci p v w := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  exact (formOperator_pairing _ v w).trans
    (tensorBilinear_apply g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 p v w)

variable {ι : Type*} [Fintype ι]

theorem ricci_orthonormal_trace (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, D.ricci p (e i) (e i)) = D.scalarCurvature p := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  intro e
  have h := bilinear_trace_basis_eq
    (tensorBilinear g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 p)
    e (g.orthonormalBasis p)
  simpa only [tensorBilinear_apply, LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, LeviCivitaData.scalarCurvature] using h

theorem ricciOperator_orthonormal_square (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, g.inner p (ricciOperator hM04 D p (e i)) (ricciOperator hM04 D p (e i))) =
        D.ricciNormSq p := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  intro e
  let B := tensorBilinear g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 p
  have h := bilinear_square_basis_eq B e (g.orthonormalBasis p)
  simp_rw [bilinear_square_contraction B e] at h
  simpa only [B, tensorBilinear_apply, LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, LeviCivitaData.ricciNormSq,
    ricciOperator] using! h

theorem curvature_orthonormal_index_trace (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (A : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, D.curvatureTensor p (e i) A A (e i)) = -D.ricci p A A := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  intro e
  have h := bilinear_trace_basis_eq
    (curvatureSliceBilinear D (hM04.tensor_calculus n M g D).1 p A A)
    e (g.orthonormalBasis p)
  simp only [curvatureSliceBilinear_apply] at h
  calc
    _ = ∑ i, -D.curvatureTensor p A (e i) A (e i) :=
      Finset.sum_congr rfl fun i _ ↦ curvatureTensor_first_antisymm hM04 D p (e i) A A (e i)
    _ = -D.ricci p A A := by rw [Finset.sum_neg_distrib, h]; rfl

theorem covariantRicci_direction_orthonormal_trace (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (A : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, ricciDerivativePairing D p A (e i) (e i)) =
        mvfderiv (𝓡 n) D.scalarCurvature p A := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  intro e
  have hRic := (hM04.tensor_calculus n M g D).2.1
  have hD := (hM04.tensor_calculus n M g D).2.2.1 2 D.ricciEvaluation hRic
  let B := bilinearOfMultilinear ((hD.1 p).choose.curryLeft A)
  have hB (v w : TangentSpace (𝓡 n) p) : B v w = ricciDerivativePairing D p A v w := by
    dsimp only [B]
    rw [bilinearOfMultilinear_apply]
    change (hD.1 p).choose ![A, v, w] = _
    exact ((hD.1 p).choose_spec ![A, v, w]).symm
  have he := bilinear_trace_basis_eq B e (g.orthonormalBasis p)
  simp only [hB] at he
  have h := tensorMetricTrace_mvfderiv D D.ricciEvaluation hRic p A
  exact he.trans h.symm

theorem covariantRicci_divergence_trace_basis_eq (hM04 : RicciFlowCurvatureTheory.{u})
    (D : LeviCivitaData g) (p : M) (A : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, ricciDerivativePairing D p (e i) A (e i)) =
        ∑ j, ricciDerivativePairing D p (g.orthonormalBasis p j) A (g.orthonormalBasis p j) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  intro e
  have hRic := (hM04.tensor_calculus n M g D).2.1
  have hD := (hM04.tensor_calculus n M g D).2.2.1 2 D.ricciEvaluation hRic
  let B := bilinearOfMultilinear ((hD.1 p).choose.curryMid (1 : Fin 3) A)
  have hB (v w : TangentSpace (𝓡 n) p) : B v w = ricciDerivativePairing D p v A w := by
    dsimp only [B]
    rw [bilinearOfMultilinear_apply]
    change (hD.1 p).choose ((1 : Fin 3).insertNth A ![v, w]) = _
    have heq : (1 : Fin 3).insertNth A ![v, w] = ![v, A, w] := by
      funext i
      fin_cases i <;> simp [Fin.insertNth, Fin.succAboveCases]
    rw [heq]
    exact ((hD.1 p).choose_spec ![v, A, w]).symm
  have h := bilinear_trace_basis_eq B e (g.orthonormalBasis p)
  simpa only [hB] using h

theorem squareTime_covariantRicci_divergence_orthonormal_trace
    {J : Set ℝ} (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (A : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, ricciDerivativePairing (F.connection (T - s ^ 2)) p (e i) A (e i)) =
        mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature p A / 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  intro e
  rw [covariantRicci_divergence_trace_basis_eq hM04 (F.connection (T - s ^ 2)) p A e]
  have h := squareTime_scalarCurvature_mvfderiv_contracted_bianchi F hM04 T b hb hwindow p s hs A
  dsimp only at h
  linarith

end PoincareConjecture.Proofs.M09
