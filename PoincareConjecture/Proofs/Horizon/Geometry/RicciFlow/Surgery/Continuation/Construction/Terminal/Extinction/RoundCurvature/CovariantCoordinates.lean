import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CoordinateFormula







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem update_pair_zero {E : Type*} (u v w : E) :
    Function.update ![u, v] 0 w = ![w, v] := by
  ext i
  fin_cases i <;> simp

private theorem update_pair_one {E : Type*} (u v w : E) :
    Function.update ![u, v] 1 w = ![u, w] := by
  ext i
  fin_cases i <;> simp

theorem covariantTensorDerivative_model_const
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : IsSmoothCovariantTensor T)
    (x a : EuclideanSpace ℝ (Fin n)) (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    D.covariantTensorDerivative T x (Fin.cons a v) =
      fderiv ℝ (fun y => T y v) x a -
        ∑ i, T x (Function.update v i
          (christoffelBilinear g.euclideanCoefficients x a (v i))) := by
  have h := D.fderiv_covariantTensor_pullback_model hT
    (q := id) (V := fun i _ => v i) (p := x) differentiableAt_id
    (fun _ => differentiableAt_const _) a
  simp only [manifoldCovDerivAlong_model, covDerivAlong, fderiv_id,
    ContinuousLinearMap.id_apply, fderiv_const_apply, zero_apply, zero_add, id_eq] at h
  linarith

theorem covariantTensorDerivative_eq_fderiv_of_christoffel_zero
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : IsSmoothCovariantTensor T)
    (x a : EuclideanSpace ℝ (Fin n)) (v : Fin k → EuclideanSpace ℝ (Fin n))
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0) :
    D.covariantTensorDerivative T x (Fin.cons a v) =
      fderiv ℝ (fun y => T y v) x a := by
  obtain ⟨A, hA⟩ := hT.1 x
  rw [D.covariantTensorDerivative_model_const hT]
  simp only [hzero, zero_apply, hA, A.map_update_zero, Finset.sum_const_zero, sub_zero]

theorem covariantTwoTensorDerivative_model_const
    (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x a u v : EuclideanSpace ℝ (Fin n)) :
    D.covariantTensorDerivative T x ![a, u, v] =
      fderiv ℝ (fun y => T y ![u, v]) x a -
        T x ![christoffelBilinear g.euclideanCoefficients x a u, v] -
        T x ![u, christoffelBilinear g.euclideanCoefficients x a v] := by
  have h := D.covariantTensorDerivative_model_const hT x a ![u, v]
  simpa [Fin.sum_univ_succ, update_pair_zero, update_pair_one,
    sub_add_eq_sub_sub] using h

private theorem tensor_constant_evaluation_contDiffAt
    {k : ℕ} {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : IsSmoothCovariantTensor T)
    (x : EuclideanSpace ℝ (Fin n)) (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun y => T y v) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply hT.contMDiffAt_apply
  intro i
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  simpa using (contMDiffAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := v i) (x := x))

private theorem tensor_fderiv_zero_left
    (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x a v : EuclideanSpace ℝ (Fin n))
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hV : DifferentiableAt ℝ V x) (hzero : V x = 0) :
    fderiv ℝ (fun y => T y ![V y, v]) x a = T x ![fderiv ℝ V x a, v] := by
  obtain ⟨A, hA⟩ := hT.1 x
  obtain ⟨B, hB⟩ := (D.covariantTensorDerivative_isSmooth hT).1 x
  have hA₀ (w : EuclideanSpace ℝ (Fin n)) : T x ![0, w] = 0 := by
    rw [hA]
    exact A.map_coord_zero 0 rfl
  have hB₀ (w z : EuclideanSpace ℝ (Fin n)) :
      D.covariantTensorDerivative T x ![w, 0, z] = 0 := by
    rw [hB]
    exact B.map_coord_zero 1 rfl
  have h := D.fderiv_covariantTensor_pullback_model hT
    (q := id) (V := ![V, fun _ => v]) (p := x) differentiableAt_id
    (by intro i; fin_cases i <;> simp [hV]) a
  have heval (y : EuclideanSpace ℝ (Fin n)) :
      (fun i => (![V, fun _ => v] : Fin 2 → _ → _) i y) = ![V y, v] := by
    ext i
    fin_cases i <;> rfl
  simp only [heval, id_eq, manifoldCovDerivAlong_model, covDerivAlong, fderiv_id,
    ContinuousLinearMap.id_apply, Fin.sum_univ_succ] at h
  have hΓ : coordinateChristoffel g.euclideanCoefficients x a 0 = 0 := by
    change christoffelBilinear g.euclideanCoefficients x a 0 = 0
    exact map_zero _
  simpa [hzero, hΓ, hA₀, hB₀, update_pair_zero, update_pair_one] using h

private theorem tensor_fderiv_zero_right
    (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x a u : EuclideanSpace ℝ (Fin n))
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hV : DifferentiableAt ℝ V x) (hzero : V x = 0) :
    fderiv ℝ (fun y => T y ![u, V y]) x a = T x ![u, fderiv ℝ V x a] := by
  obtain ⟨A, hA⟩ := hT.1 x
  obtain ⟨B, hB⟩ := (D.covariantTensorDerivative_isSmooth hT).1 x
  have hA₀ (w : EuclideanSpace ℝ (Fin n)) : T x ![w, 0] = 0 := by
    rw [hA]
    exact A.map_coord_zero 1 rfl
  have hB₀ (w z : EuclideanSpace ℝ (Fin n)) :
      D.covariantTensorDerivative T x ![w, z, 0] = 0 := by
    rw [hB]
    exact B.map_coord_zero 2 rfl
  have h := D.fderiv_covariantTensor_pullback_model hT
    (q := id) (V := ![fun _ => u, V]) (p := x) differentiableAt_id
    (by intro i; fin_cases i <;> simp [hV]) a
  have heval (y : EuclideanSpace ℝ (Fin n)) :
      (fun i => (![fun _ => u, V] : Fin 2 → _ → _) i y) = ![u, V y] := by
    ext i
    fin_cases i <;> rfl
  simp only [heval, id_eq, manifoldCovDerivAlong_model, covDerivAlong, fderiv_id,
    ContinuousLinearMap.id_apply, Fin.sum_univ_succ] at h
  have hΓ : coordinateChristoffel g.euclideanCoefficients x a 0 = 0 := by
    change christoffelBilinear g.euclideanCoefficients x a 0 = 0
    exact map_zero _
  simpa [hzero, hΓ, hA₀, hB₀, update_pair_zero, update_pair_one] using h

private theorem tensor_evaluation_contDiffAt
    {k : ℕ} {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) k}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin n))
    (V : Fin k → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hV : ∀ i, ContDiffAt ℝ ∞ (V i) x) :
    ContDiffAt ℝ ∞ (fun y => T y (fun i => V i y)) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply hT.contMDiffAt_apply
  intro i
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  simpa using contMDiffAt_iff_contDiffAt.mpr (hV i)



theorem covariantTwoTensorSecondDerivative_of_christoffel_zero
    (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x a b u v : EuclideanSpace ℝ (Fin n))
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0) :
    D.covariantTensorDerivative (D.covariantTensorDerivative T) x ![a, b, u, v] =
      fderiv ℝ (fun y => fderiv ℝ (fun z => T z ![u, v]) y b) x a -
        T x ![fderiv ℝ (fun y => christoffelBilinear g.euclideanCoefficients y b u) x a, v] -
        T x ![u, fderiv ℝ (fun y => christoffelBilinear g.euclideanCoefficients y b v) x a] := by
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiffAt ℝ ∞ Γ x :=
    contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
      (g.inner_isInvertible x)
  have hΓuv (w : EuclideanSpace ℝ (Fin n)) : ContDiffAt ℝ ∞ (fun y => Γ y b w) x :=
    (hΓ.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hΓzero (w : EuclideanSpace ℝ (Fin n)) : Γ x b w = 0 := by
    simp only [Γ, hzero, zero_apply]
  have hleft : ContDiffAt ℝ ∞ (fun y => T y ![Γ y b u, v]) x := by
    have h := tensor_evaluation_contDiffAt hT x ![fun y => Γ y b u, fun _ => v]
      (by intro i; fin_cases i; exact hΓuv u; exact contDiffAt_const)
    convert h using 1
    funext y
    congr 1
    ext i
    fin_cases i <;> rfl
  have hright : ContDiffAt ℝ ∞ (fun y => T y ![u, Γ y b v]) x := by
    have h := tensor_evaluation_contDiffAt hT x ![fun _ => u, fun y => Γ y b v]
      (by intro i; fin_cases i; exact contDiffAt_const; exact hΓuv v)
    convert h using 1
    funext y
    congr 1
    ext i
    fin_cases i <;> rfl
  have hfirst : ContDiffAt ℝ ∞
      (fun y => fderiv ℝ (fun z => T z ![u, v]) y b) x :=
    ((tensor_constant_evaluation_contDiffAt hT x ![u, v]).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiffAt_const
  erw [D.covariantTensorDerivative_eq_fderiv_of_christoffel_zero
    (D.covariantTensorDerivative_isSmooth hT) x a ![b, u, v] hzero]
  have heq : (fun y => D.covariantTensorDerivative T y ![b, u, v]) =
      (fun y => fderiv ℝ (fun z => T z ![u, v]) y b -
        T y ![Γ y b u, v] - T y ![u, Γ y b v]) :=
    funext fun y => D.covariantTwoTensorDerivative_model_const hT y b u v
  erw [heq, fderiv_fun_sub
    ((hfirst.differentiableAt (by simp)).sub (hleft.differentiableAt (by simp)))
    (hright.differentiableAt (by simp)),
    fderiv_fun_sub (hfirst.differentiableAt (by simp)) (hleft.differentiableAt (by simp))]
  simp only [sub_apply]
  erw [D.tensor_fderiv_zero_left hT x a v ((hΓuv u).differentiableAt (by simp)) (hΓzero u),
    D.tensor_fderiv_zero_right hT x a u ((hΓuv v).differentiableAt (by simp)) (hΓzero v)]



theorem alternatingSecondDerivative_eq_covariant_add_curvature
    (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x u b v c : EuclideanSpace ℝ (Fin n))
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0) :
    let S := fun a b u v => fderiv ℝ (fun y => fderiv ℝ (fun z => T z ![u, v]) y b) x a
    let C := fun a b u v =>
      D.covariantTensorDerivative (D.covariantTensorDerivative T) x ![a, b, u, v]
    S u c b v - S u v b c - S b c u v + S b v u c =
      C u c b v - C u v b c - C b c u v + C b v u c +
        T x ![D.curvature x u b c, v] - T x ![D.curvature x u b v, c] := by
  dsimp only
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiffAt ℝ ∞ Γ x :=
    contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
      (g.inner_isInvertible x)
  have happly (a p q : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => Γ y p q) x a = fderiv ℝ Γ x a p q := by
    have h := (((hΓ.differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const p x)).clm_apply (hasFDerivAt_const q x)).fderiv
    simpa using congrArg (fun L => L a) h
  have hcurv (a p q : EuclideanSpace ℝ (Fin n)) :
      D.curvature x a p q =
        fderiv ℝ (fun y => Γ y p q) x a - fderiv ℝ (fun y => Γ y a q) x p := by
    rw [← coordinateCurvature_eq_retained D,
      coordinateCurvature_eq_christoffelCurvature (hΓ.differentiableAt (by simp))]
    simp only [christoffelCurvature, happly, Γ, hzero, zero_apply, add_zero, sub_zero]
  have hswap (a p q : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => Γ y p q) x a = fderiv ℝ (fun y => Γ y q p) x a := by
    congr 2
    funext y
    exact christoffelBilinear_symm
      ((g.contDiffAt_euclideanCoefficients y).differentiableAt (by simp))
      (Filter.Eventually.of_forall (fun z p q => g.symm z p q)) p q
  obtain ⟨A, hA⟩ := hT.1 x
  have hsub (p q r : EuclideanSpace ℝ (Fin n)) :
      T x ![p - q, r] = T x ![p, r] - T x ![q, r] := by
    simpa only [hA, update_pair_zero] using A.map_update_sub ![p, r] 0 p q
  have h₁ := D.covariantTwoTensorSecondDerivative_of_christoffel_zero hT x u c b v hzero
  have h₂ := D.covariantTwoTensorSecondDerivative_of_christoffel_zero hT x u v b c hzero
  have h₃ := D.covariantTwoTensorSecondDerivative_of_christoffel_zero hT x b c u v hzero
  have h₄ := D.covariantTwoTensorSecondDerivative_of_christoffel_zero hT x b v u c hzero
  erw [hcurv, hcurv, hsub, hsub]
  erw [hswap u c b, hswap u c v] at h₁
  erw [hswap u v b] at h₂
  erw [hswap b c u, hswap b c v] at h₃
  erw [hswap b v u] at h₄
  linarith

end PoincareConjecture.LeviCivitaData
