import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M35

open CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finite_inverse_metric_jets {ι : Type*} {U : Set E} {n : ℕ}
    (hU : IsOpen U) {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hjets : HasUniformJetBoundsOn n U A) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) :
    HasUniformJetBoundsOn n U (fun i x => (A i x).inverse) := by
  obtain ⟨C, hC⟩ := hjets 0 (Nat.zero_le _)
  let K := {B : E →L[ℝ] E →L[ℝ] ℝ | ‖B‖ ≤ C ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v}
  apply hjets.comp_fixed_at hU (isCompact_bounded_uniformlyElliptic a C)
    (fun i => (hA i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    (fun B hB => (isInvertible_of_uniformEllipticity ha hB.2).contDiffAt_map_inverse)
  intro i x hx
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using hC i x hx, hell i x hx⟩

noncomputable def finiteKoszulOperator :
    (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  let flipT :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toLinearIsometry.toContinuousLinearMap
  let C := ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
    (E →L[ℝ] E →L[ℝ] ℝ) flipL
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + flipT.comp C - C.comp flipT)

noncomputable def finiteChristoffelContraction :
    ((E →L[ℝ] ℝ) →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)

theorem finite_christoffel_jets {ι : Type*} {U : Set E} {n : ℕ}
    (hU : IsOpen U) {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hjets : HasUniformJetBoundsOn (n + 1) U A) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) :
    HasUniformJetBoundsOn n U
      (fun i => CoordinateExponential.christoffelBilinear (A i)) := by
  have hD : ∀ i, ContDiffOn ℝ ∞ (fderiv ℝ (A i)) U :=
    fun i => (hA i).fderiv_of_isOpen hU (by simp)
  have hK : ∀ i, ContDiffOn ℝ ∞
      (fun x => finiteKoszulOperator (fderiv ℝ (A i) x)) U :=
    fun i => finiteKoszulOperator.contDiff.comp_contDiffOn (hD i)
  have hjK := hjets.fderiv.clm hU hD finiteKoszulOperator
  have hjI := finite_inverse_metric_jets hU hA
    (hjets.mono_order (Nat.le_succ n)) ha hell
  have hjC := hjI.bilinear hU hjK
    (contDiffOn_inverse_metric hU hA ha hell) hK finiteChristoffelContraction
  exact hjC.congr hU fun _ _ _ => rfl

omit [FiniteDimensional ℝ E] in

theorem finite_jets_of_christoffel_hessian {ι : Type*} {U V : Set E} {r : ℕ}
    (hU : IsOpen U) (hV : IsOpen V)
    {f : ι → E → E} {A B : ι → E → E →L[ℝ] E →L[ℝ] E}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hmap : ∀ i, MapsTo (f i) U V)
    (hAj : HasUniformJetBoundsOn r U A) (hBj : HasUniformJetBoundsOn r V B)
    (hzero : ∃ C : ℝ, ∀ i x, x ∈ U → ‖f i x‖ ≤ C)
    (hfirst : ∃ C : ℝ, ∀ i x, x ∈ U → ‖fderiv ℝ (f i) x‖ ≤ C)
    (hEq : ∀ i x, x ∈ U → ∀ u v,
      fderiv ℝ (fderiv ℝ (f i)) x u v =
        fderiv ℝ (f i) x (A i x u v) -
          B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v)) :
    HasUniformJetBoundsOn (r + 2) U f := by
  let D := fun i => fderiv ℝ (f i)
  have hD : ∀ i, ContDiffOn ℝ ∞ (D i) U :=
    fun i => (hf i).fderiv_of_isOpen hU (by simp)
  have hBc : ∀ i, ContDiffOn ℝ ∞ (fun x => B i (f i x)) U :=
    fun i => (hB i).comp (hf i) (hmap i)
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toLinearIsometry.toContinuousLinearMap
  have hDj : ∀ n ≤ r + 1, HasUniformJetBoundsOn n U D := by
    intro n
    induction n with
    | zero =>
      intro _ m hm
      have : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      simpa only [norm_iteratedFDeriv_zero] using hfirst
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hfj : HasUniformJetBoundsOn n U f :=
        (HasUniformJetBoundsOn.succ_of_fderiv hzero hi).mono_order (Nat.le_succ n)
      have hBfj : HasUniformJetBoundsOn n U (fun i x => B i (f i x)) :=
        hfj.comp hU hV (hBj.mono_order (by omega))
          (fun i => (hf i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
          (fun i => (hB i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) hmap
      have hpost := hi.clm hU hD (ContinuousLinearMap.compL ℝ E E E)
      have hcpost : ∀ i, ContDiffOn ℝ ∞
          (fun x => ContinuousLinearMap.compL ℝ E E E (D i x)) U :=
        fun i => (ContinuousLinearMap.compL ℝ E E E).contDiff.comp_contDiffOn (hD i)
      have hleft := hpost.clm_comp hU (hAj.mono_order (by omega)) hcpost hA
      have hpre := hBfj.clm_comp hU hi hBc hD
      have hcpre : ∀ i, ContDiffOn ℝ ∞ (fun x => (B i (f i x)).comp (D i x)) U :=
        fun i => (hBc i).clm_comp (hD i)
      have hflip := hpre.clm hU hcpre flipL
      have hcflip : ∀ i, ContDiffOn ℝ ∞
          (fun x => flipL ((B i (f i x)).comp (D i x))) U :=
        fun i => flipL.contDiff.comp_contDiffOn (hcpre i)
      have hpre' := hflip.clm_comp hU hi hcflip hD
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
  exact HasUniformJetBoundsOn.succ_of_fderiv hzero (hDj (r + 1) le_rfl)

theorem finite_local_isometry_jets {ι : Type*} {U V : Set E} {n : ℕ}
    (hU : IsOpen U) (hV : IsOpen V) (hVbounded : Bornology.IsBounded V)
    {A B : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {f : ι → E → E}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hBsymm : ∀ i x, x ∈ V → ∀ u v, B i x u v = B i x v u)
    {a : ℝ} (ha : 0 < a)
    (hAlow : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v)
    (hBlow : ∀ i x, x ∈ V → ∀ v, a * ‖v‖ ^ 2 ≤ B i x v v)
    (hAj : HasUniformJetBoundsOn (n + 1) U A)
    (hBj : HasUniformJetBoundsOn (n + 1) V B)
    (hmap : ∀ i, MapsTo (f i) U V)
    (hmetric : ∀ i x, x ∈ U → ∀ u v,
      B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v) = A i x u v) :
    HasUniformJetBoundsOn (n + 2) U f := by
  let GA : ι → E → E →L[ℝ] E →L[ℝ] E :=
    fun i => CoordinateExponential.christoffelBilinear (A i)
  let GB : ι → E → E →L[ℝ] E →L[ℝ] E :=
    fun i => CoordinateExponential.christoffelBilinear (B i)
  obtain ⟨C0, hC0⟩ := hVbounded.exists_norm_le
  have hzero : ∃ C : ℝ, ∀ i x, x ∈ U → ‖f i x‖ ≤ C :=
    ⟨C0, fun i x hx => hC0 (f i x) (hmap i hx)⟩
  obtain ⟨CA, hCA⟩ := hAj 0 (Nat.zero_le _)
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
  have hGA : HasUniformJetBoundsOn n U GA := finite_christoffel_jets hU hA hAj ha hAlow
  have hGB : HasUniformJetBoundsOn n V GB := finite_christoffel_jets hV hB hBj ha hBlow
  have hsGA : ∀ i, ContDiffOn ℝ ∞ (GA i) U :=
    contDiffOn_christoffelBilinear_of_uniformEllipticity hU hA ha hAlow
  have hsGB : ∀ i, ContDiffOn ℝ ∞ (GB i) V :=
    contDiffOn_christoffelBilinear_of_uniformEllipticity hV hB ha hBlow
  apply finite_jets_of_christoffel_hessian hU hV hf hsGA hsGB hmap hGA hGB hzero hfirst
  intro i x hx u v
  have hAi := fun y hy => isInvertible_of_uniformEllipticity ha (hAlow i y hy)
  have hBi := fun y hy => isInvertible_of_uniformEllipticity ha (hBlow i y hy)
  have hH := fderiv_fderiv_eq_transitionHessianPolynomial_on hU hV (hA i) (hB i)
    hAi hBi (hBsymm i) (hf i) (hmap i)
    (fun y hy => surjective_of_pullback_isInvertible (hAi y hy)
      (fun u v => (hmetric i y hy u v).symm))
    (fun y hy u v => (hmetric i y hy u v).symm) hx
  simpa [GA, GB] using congrArg (fun L => L u v) hH

end PoincareConjecture.M35
