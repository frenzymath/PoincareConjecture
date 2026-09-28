import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.ChangeCoordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.JetBounds.Operations
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.Hessian
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelBounds
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def transitionHessianField
    [CompleteSpace E]
    (A B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : E × (E × (E →L[ℝ] E))) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E E E z.2.2).comp
      (CoordinateExponential.christoffelBilinear A z.1) -
    (CoordinateExponential.christoffelBilinear B z.2.1).bilinearComp z.2.2 z.2.2

@[simp] theorem transitionHessianField_apply
    [CompleteSpace E]
    (A B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x y : E) (D : E →L[ℝ] E) (u v : E) :
    transitionHessianField A B (x, (y, D)) u v =
      D (coordinateChristoffel A x u v) -
        coordinateChristoffel B y (D u) (D v) := by
  rfl

theorem contDiff_transitionHessianField
    [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {A B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hAi : ∀ x, (A x).IsInvertible)
    (hBi : ∀ x, (B x).IsInvertible) :
    ContDiff ℝ ∞ (transitionHessianField A B) := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  change ContDiff ℝ ∞ (fun z : E × (E × (E →L[ℝ] E)) =>
    z.2.2 (coordinateChristoffel A z.1 u v) -
      coordinateChristoffel B z.2.1 (z.2.2 u) (z.2.2 v))
  have hCA : ContDiff ℝ ∞ (CoordinateExponential.christoffelBilinear A) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact CoordinateExponential.contDiffAt_christoffelBilinear
      (hA.contDiffAt) (hAi z)
  have hCB : ContDiff ℝ ∞ (CoordinateExponential.christoffelBilinear B) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact CoordinateExponential.contDiffAt_christoffelBilinear
      (hB.contDiffAt) (hBi z)
  have hD : ContDiff ℝ ∞ (fun z : E × (E × (E →L[ℝ] E)) => z.2.2) :=
    contDiff_snd.comp contDiff_snd
  exact (hD.clm_apply (((hCA.comp contDiff_fst).clm_apply contDiff_const).clm_apply
    contDiff_const)).sub
    ((((hCB.comp (contDiff_fst.comp contDiff_snd)).clm_apply
      (hD.clm_apply contDiff_const)).clm_apply
        (hD.clm_apply contDiff_const)))

theorem norm_le_of_pullback_quadratic_bounds
    (A : E →L[ℝ] E →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ) (D : E →L[ℝ] F)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hA : ∀ v : E, A v v ≤ C * ‖v‖ ^ 2)
    (hB : ∀ w : F, a * ‖w‖ ^ 2 ≤ B w w)
    (hmetric : ∀ v w : E, B (D v) (D w) = A v w) :
    ‖D‖ ≤ Real.sqrt (C / a) := by
  have hratio : 0 ≤ C / a := div_nonneg hC ha.le
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hquad : a * ‖D v‖ ^ 2 ≤ C * ‖v‖ ^ 2 := by
    calc
      a * ‖D v‖ ^ 2 ≤ B (D v) (D v) := hB _
      _ = A v v := hmetric v v
      _ ≤ C * ‖v‖ ^ 2 := hA v
  have hsq : ‖D v‖ ^ 2 ≤ (Real.sqrt (C / a) * ‖v‖) ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left ha).mp
    calc
      a * ‖D v‖ ^ 2 ≤ C * ‖v‖ ^ 2 := hquad
      _ = a * ((Real.sqrt (C / a) * ‖v‖) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hratio]
        field_simp
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

theorem norm_fderiv_le_of_pullback_quadratic_bounds
    {U : Set E} {V : Set F} {f : E → F}
    {A : E → E →L[ℝ] E →L[ℝ] ℝ} {B : F → F →L[ℝ] F →L[ℝ] ℝ}
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hfV : MapsTo f U V)
    (hA : ∀ x ∈ U, ∀ v : E, A x v v ≤ C * ‖v‖ ^ 2)
    (hB : ∀ y ∈ V, ∀ w : F, a * ‖w‖ ^ 2 ≤ B y w w)
    (hmetric : ∀ x ∈ U, ∀ v w : E,
      B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w) :
    ∀ x ∈ U, ‖fderiv ℝ f x‖ ≤ Real.sqrt (C / a) := by
  intro x hx
  exact norm_le_of_pullback_quadratic_bounds (A x) (B (f x)) (fderiv ℝ f x)
    ha hC (hA x hx) (hB (f x) (hfV hx)) (hmetric x hx)

theorem hasUniformJetBounds_of_hessian
    {ι : Type*} {n : ℕ} {f : ι → E → F} {H : ι → E → E →L[ℝ] F}
    (hzero : ∃ C : ℝ, ∀ i x, ‖f i x‖ ≤ C)
    (hH : ∀ n, HasUniformJetBounds n H)
    (hEq : ∀ i, fderiv ℝ (f i) = H i) :
    ∀ n, HasUniformJetBounds n f := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0
      simpa only [norm_iteratedFDeriv_zero] using hzero
  | succ n ih =>
      exact HasUniformJetBounds.succ_of_fderiv hzero (by
        intro m hm
        obtain ⟨C, hC⟩ := hH n m hm
        refine ⟨C, ?_⟩
        intro i x
        simpa only [hEq i] using hC i x)

theorem hasUniformJetBoundsOn_of_christoffel_hessian
    {ι : Type*} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : ι → E → E} {A B : ι → E → E →L[ℝ] E →L[ℝ] E}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hmap : ∀ i, MapsTo (f i) U V)
    (hAj : ∀ n, HasUniformJetBoundsOn n U A)
    (hBj : ∀ n, HasUniformJetBoundsOn n V B)
    (hzero : ∃ C : ℝ, ∀ i x, x ∈ U → ‖f i x‖ ≤ C)
    (hfirst : ∃ C : ℝ, ∀ i x, x ∈ U → ‖fderiv ℝ (f i) x‖ ≤ C)
    (hEq : ∀ i x, x ∈ U → ∀ u v,
      fderiv ℝ (fderiv ℝ (f i)) x u v =
        fderiv ℝ (f i) x (A i x u v) -
          B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v)) :
    ∀ n, HasUniformJetBoundsOn n U f := by
  let D := fun i => fderiv ℝ (f i)
  have hD : ∀ i, ContDiffOn ℝ ∞ (D i) U :=
    fun i => (hf i).fderiv_of_isOpen hU (by simp)
  have hBc : ∀ i, ContDiffOn ℝ ∞ (fun x => B i (f i x)) U :=
    fun i => (hB i).comp (hf i) (hmap i)
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toLinearIsometry.toContinuousLinearMap
  have hDj : ∀ n, HasUniformJetBoundsOn n U D := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have : m = 0 := Nat.eq_zero_of_le_zero hm
        subst m
        simpa only [norm_iteratedFDeriv_zero] using hfirst
    | succ n ih =>
        have hfj : HasUniformJetBoundsOn n U f :=
          (HasUniformJetBoundsOn.succ_of_fderiv hzero ih).mono_order (Nat.le_succ n)
        have hBfj : HasUniformJetBoundsOn n U (fun i x => B i (f i x)) :=
          hfj.comp hU hV (hBj n)
            (fun i => (hf i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
            (fun i => (hB i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) hmap
        have hpost := ih.clm hU hD (ContinuousLinearMap.compL ℝ E E E)
        have hcpost : ∀ i, ContDiffOn ℝ ∞
            (fun x => ContinuousLinearMap.compL ℝ E E E (D i x)) U :=
          fun i => (ContinuousLinearMap.compL ℝ E E E).contDiff.comp_contDiffOn (hD i)
        have hleft := hpost.clm_comp hU (hAj n) hcpost hA
        have hpre := hBfj.clm_comp hU ih hBc hD
        have hcpre : ∀ i, ContDiffOn ℝ ∞ (fun x => (B i (f i x)).comp (D i x)) U :=
          fun i => (hBc i).clm_comp (hD i)
        have hflip := hpre.clm hU hcpre flipL
        have hcflip : ∀ i, ContDiffOn ℝ ∞
            (fun x => flipL ((B i (f i x)).comp (D i x))) U :=
          fun i => flipL.contDiff.comp_contDiffOn (hcpre i)
        have hpre' := hflip.clm_comp hU ih hcflip hD
        have hcpre' : ∀ i, ContDiffOn ℝ ∞
            (fun x => (flipL ((B i (f i x)).comp (D i x))).comp (D i x)) U :=
          fun i => (hcflip i).clm_comp (hD i)
        have hright := hpre'.clm hU hcpre' flipL
        have hcleft : ∀ i, ContDiffOn ℝ ∞
            (fun x => (ContinuousLinearMap.compL ℝ E E E (D i x)).comp (A i x)) U :=
          fun i => (hcpost i).clm_comp (hA i)
        have hcright : ∀ i, ContDiffOn ℝ ∞
            (fun x => flipL ((flipL ((B i (f i x)).comp (D i x))).comp (D i x))) U :=
          fun i => flipL.contDiff.comp_contDiffOn (hcpre' i)
        apply HasUniformJetBoundsOn.succ_of_fderiv hfirst
        apply (hleft.sub hU hright hcleft hcright).congr hU
        intro i x hx
        ext u v
        exact (hEq i x hx u v).symm
  intro n
  exact (HasUniformJetBoundsOn.succ_of_fderiv hzero (hDj n)).mono_order (Nat.le_succ n)

theorem uniform_derivative_bounds_of_local_isometries
    {d : ℕ} {U V : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hV : IsOpen V) (hVbounded : Bornology.IsBounded V)
    {A B : ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hAsymm : ∀ i x, x ∈ U → ∀ u v, A i x u v = A i x v u)
    (hBsymm : ∀ i x, x ∈ V → ∀ u v, B i x u v = B i x v u)
    {a : ℝ} (ha : 0 < a)
    (hAlow : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v)
    (hBlow : ∀ i x, x ∈ V → ∀ v, a * ‖v‖ ^ 2 ≤ B i x v v)
    (hjets : ∀ m : ℕ, ∃ C : ℝ,
      (∀ i x, x ∈ U → ‖iteratedFDeriv ℝ m (A i) x‖ ≤ C) ∧
      (∀ i x, x ∈ V → ‖iteratedFDeriv ℝ m (B i) x‖ ≤ C))
    (hmap : ∀ i, MapsTo (f i) U V)
    (hmetric : ∀ i x, x ∈ U → ∀ u v,
      B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v) = A i x u v) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ i x, x ∈ U →
      ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin d)
  let ΓA : ℕ → E → E →L[ℝ] E →L[ℝ] E :=
    fun i => CoordinateExponential.christoffelBilinear (A i)
  let ΓB : ℕ → E → E →L[ℝ] E →L[ℝ] E :=
    fun i => CoordinateExponential.christoffelBilinear (B i)
  have hAj : ∀ n, HasUniformJetBoundsOn n U A := by
    intro n m hm
    obtain ⟨C, hCA, _⟩ := hjets m
    exact ⟨C, fun i x hx => hCA i x hx⟩
  have hBj : ∀ n, HasUniformJetBoundsOn n V B := by
    intro n m hm
    obtain ⟨C, _, hCB⟩ := hjets m
    exact ⟨C, fun i x hx => hCB i x hx⟩
  obtain ⟨C0, hC0⟩ := hVbounded.exists_norm_le
  have hzero : ∃ C : ℝ, ∀ i x, x ∈ U → ‖f i x‖ ≤ C :=
    ⟨C0, fun i x hx => hC0 (f i x) (hmap i hx)⟩
  obtain ⟨CA, hCA⟩ := (hAj 0) 0 le_rfl
  have hfirst : ∃ C : ℝ, ∀ i x, x ∈ U → ‖fderiv ℝ (f i) x‖ ≤ C := by
    refine ⟨Real.sqrt (max CA 0 / a), fun i x hx => ?_⟩
    apply norm_le_of_pullback_quadratic_bounds (A i x) (B i (f i x))
      (fderiv ℝ (f i) x) ha (le_max_right _ _)
      (fun v => ?_) (hBlow i (f i x) (hmap i hx)) (hmetric i x hx)
    have hnorm : ‖A i x‖ ≤ max CA 0 :=
      (by simpa only [norm_iteratedFDeriv_zero] using hCA i x hx : ‖A i x‖ ≤ CA).trans
        (le_max_left _ _)
    calc
      A i x v v ≤ ‖A i x v v‖ := le_abs_self _
      _ ≤ ‖A i x‖ * (‖v‖ * ‖v‖) := by
        simpa only [mul_assoc] using (A i x).le_opNorm₂ v v
      _ ≤ max CA 0 * (‖v‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = max CA 0 * ‖v‖ ^ 2 := by rw [pow_two]
  have hΓA : ∀ n, HasUniformJetBoundsOn n U ΓA := by
    intro n
    exact hasUniformJetBoundsOn_christoffelBilinear hU hA hAj ha hAlow n
  have hΓB : ∀ n, HasUniformJetBoundsOn n V ΓB := by
    intro n
    exact hasUniformJetBoundsOn_christoffelBilinear hV hB hBj ha hBlow n
  have hsΓA : ∀ i, ContDiffOn ℝ ∞ (ΓA i) U := by
    intro i; exact contDiffOn_christoffelBilinear_of_uniformEllipticity hU hA ha hAlow i
  have hsΓB : ∀ i, ContDiffOn ℝ ∞ (ΓB i) V := by
    intro i; exact contDiffOn_christoffelBilinear_of_uniformEllipticity hV hB ha hBlow i
  have hF := hasUniformJetBoundsOn_of_christoffel_hessian hU hV hf
    hsΓA hsΓB hmap hΓA hΓB hzero hfirst
    (fun i x hx u v => by
      have hAi := fun y hy => isInvertible_of_uniformEllipticity ha (hAlow i y hy)
      have hBi := fun y hy => isInvertible_of_uniformEllipticity ha (hBlow i y hy)
      have hH := fderiv_fderiv_eq_transitionHessianPolynomial_on hU hV (hA i) (hB i)
        hAi hBi (hBsymm i) (hf i) (hmap i)
        (fun y hy => surjective_of_pullback_isInvertible (hAi y hy)
          (fun u v => (hmetric i y hy u v).symm))
        (fun y hy u v => (hmetric i y hy u v).symm) hx
      simpa [ΓA, ΓB] using congrArg (fun L => L u v) hH)
  intro m
  obtain ⟨C, hC⟩ := hF m m le_rfl
  exact ⟨C, fun i x hx => hC i x hx⟩

theorem exists_smoothSubsequenceExtraction_of_local_isometries
    {d : ℕ} {U V : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hV : IsOpen V) (hVbounded : Bornology.IsBounded V)
    {A B : ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hAsymm : ∀ i x, x ∈ U → ∀ u v, A i x u v = A i x v u)
    (hBsymm : ∀ i x, x ∈ V → ∀ u v, B i x u v = B i x v u)
    {a : ℝ} (ha : 0 < a)
    (hAlow : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v)
    (hBlow : ∀ i x, x ∈ V → ∀ v, a * ‖v‖ ^ 2 ≤ B i x v v)
    (hjets : ∀ m : ℕ, ∃ C : ℝ,
      (∀ i x, x ∈ U → ‖iteratedFDeriv ℝ m (A i) x‖ ≤ C) ∧
      (∀ i x, x ∈ V → ‖iteratedFDeriv ℝ m (B i) x‖ ≤ C))
    (hmap : ∀ i, MapsTo (f i) U V)
    (hmetric : ∀ i x, x ∈ U → ∀ u v,
      B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v) = A i x u v) :
    Nonempty (Poincare.Analysis.Calculus.SmoothSubsequenceExtraction U f) := by
  have hbound := uniform_derivative_bounds_of_local_isometries hU hV hVbounded
    hA hB hf hAsymm hBsymm ha hAlow hBlow hjets hmap hmetric
  apply Poincare.Analysis.Calculus.exists_smoothSubsequenceExtraction hU f hf
  intro K _ hKU m
  obtain ⟨C, hC⟩ := hbound m
  exact ⟨C, Eventually.of_forall (fun i x hx => hC i x (hKU hx))⟩

end PoincareConjecture.CoordinateTransition
