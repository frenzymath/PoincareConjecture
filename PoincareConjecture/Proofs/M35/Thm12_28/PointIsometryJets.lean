import PoincareConjecture.Proofs.M35.Mathlib.PointJetBounds
import PoincareConjecture.Proofs.M35.Thm12_28.FiniteIsometryJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35

open CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem finite_inverse_metric_jets_at {ι : Type*} {n : ℕ}
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {p : ι → E}
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (p i))
    (hjets : HasUniformJetBoundsAt n A p) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (p i) v v) :
    HasUniformJetBoundsAt n (fun i x => (A i x).inverse) p := by
  obtain ⟨C, hC⟩ := hjets 0 (Nat.zero_le _)
  apply hjets.comp_fixed hA (isCompact_bounded_uniformlyElliptic a C)
    (fun B hB => (isInvertible_of_uniformEllipticity ha hB.2).contDiffAt_map_inverse)
  intro i
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using hC i, hell i⟩



theorem finite_christoffel_jets_at {ι : Type*} {n : ℕ}
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {p : ι → E}
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (p i))
    (hjets : HasUniformJetBoundsAt (n + 1) A p) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (p i) v v) :
    HasUniformJetBoundsAt n (fun i => CoordinateExponential.christoffelBilinear (A i)) p := by
  have hD : ∀ i, ContDiffAt ℝ ∞ (fderiv ℝ (A i)) (p i) :=
    fun i => (hA i).fderiv_right (by simp)
  have hK : ∀ i, ContDiffAt ℝ ∞
      (fun x => finiteKoszulOperator (fderiv ℝ (A i) x)) (p i) :=
    fun i => finiteKoszulOperator.contDiff.contDiffAt.comp (p i) (hD i)
  have hjK := hjets.fderiv.clm hD finiteKoszulOperator
  have hjI := finite_inverse_metric_jets_at hA (hjets.mono_order (Nat.le_succ n)) ha hell
  have hI : ∀ i, ContDiffAt ℝ ∞ (fun x => (A i x).inverse) (p i) :=
    fun i => (isInvertible_of_uniformEllipticity ha (hell i)).contDiffAt_map_inverse.comp
      (p i) (hA i)
  exact hjI.bilinear hjK hI hK finiteChristoffelContraction

omit [FiniteDimensional ℝ E] in


theorem finite_jets_at_of_christoffel_hessian {ι : Type*} {r : ℕ}
    {f : ι → E → E} {A B : ι → E → E →L[ℝ] E →L[ℝ] E} {p : ι → E}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i))
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (p i))
    (hB : ∀ i, ContDiffAt ℝ ∞ (B i) (f i (p i)))
    (hAj : HasUniformJetBoundsAt r A p)
    (hBj : HasUniformJetBoundsAt r B (fun i => f i (p i)))
    (hzero : ∃ C : ℝ, ∀ i, ‖f i (p i)‖ ≤ C)
    (hfirst : ∃ C : ℝ, ∀ i, ‖fderiv ℝ (f i) (p i)‖ ≤ C)
    (hEq : ∀ i, fderiv ℝ (fderiv ℝ (f i)) =ᶠ[𝓝 (p i)]
      (fun x => transitionHessianPolynomial (A i x, (B i (f i x), fderiv ℝ (f i) x)))) :
    HasUniformJetBoundsAt (r + 2) f p := by
  let D := fun i => fderiv ℝ (f i)
  have hD : ∀ i, ContDiffAt ℝ ∞ (D i) (p i) :=
    fun i => (hf i).fderiv_right (by simp)
  have hBc : ∀ i, ContDiffAt ℝ ∞ (fun x => B i (f i x)) (p i) :=
    fun i => (hB i).comp (p i) (hf i)
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toLinearIsometry.toContinuousLinearMap
  have hDj : ∀ n ≤ r + 1, HasUniformJetBoundsAt n D p := by
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
      have hfj : HasUniformJetBoundsAt n f p :=
        (HasUniformJetBoundsAt.succ_of_fderiv hzero hi).mono_order (Nat.le_succ n)
      have hBfj : HasUniformJetBoundsAt n (fun i x => B i (f i x)) p :=
        hfj.comp (hBj.mono_order (by omega)) hf hB
      have hpost := hi.clm hD (ContinuousLinearMap.compL ℝ E E E)
      have hcpost : ∀ i, ContDiffAt ℝ ∞
          (fun x => ContinuousLinearMap.compL ℝ E E E (D i x)) (p i) :=
        fun i => (ContinuousLinearMap.compL ℝ E E E).contDiff.contDiffAt.comp (p i) (hD i)
      have hleft := hpost.clm_comp (hAj.mono_order (by omega)) hcpost hA
      have hpre := hBfj.clm_comp hi hBc hD
      have hcpre : ∀ i, ContDiffAt ℝ ∞ (fun x => (B i (f i x)).comp (D i x)) (p i) :=
        fun i => (hBc i).clm_comp (hD i)
      have hflip := hpre.clm hcpre flipL
      have hcflip : ∀ i, ContDiffAt ℝ ∞
          (fun x => flipL ((B i (f i x)).comp (D i x))) (p i) :=
        fun i => flipL.contDiff.contDiffAt.comp (p i) (hcpre i)
      have hpre' := hflip.clm_comp hi hcflip hD
      have hcpre' : ∀ i, ContDiffAt ℝ ∞
          (fun x => (flipL ((B i (f i x)).comp (D i x))).comp (D i x)) (p i) :=
        fun i => (hcflip i).clm_comp (hD i)
      have hright := hpre'.clm hcpre' flipL
      have hcleft : ∀ i, ContDiffAt ℝ ∞
          (fun x => (ContinuousLinearMap.compL ℝ E E E (D i x)).comp (A i x)) (p i) :=
        fun i => (hcpost i).clm_comp (hA i)
      have hcright : ∀ i, ContDiffAt ℝ ∞
          (fun x => flipL ((flipL ((B i (f i x)).comp (D i x))).comp (D i x))) (p i) :=
        fun i => flipL.contDiff.contDiffAt.comp (p i) (hcpre' i)
      apply HasUniformJetBoundsAt.succ_of_fderiv hfirst
      apply (hleft.sub hright hcleft hcright).congr
      intro i
      filter_upwards [hEq i] with y hy
      ext u v
      exact congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L u v) hy.symm
  exact HasUniformJetBoundsAt.succ_of_fderiv hzero (hDj (r + 1) le_rfl)




theorem finite_local_isometry_jets_at {ι : Type*} {n : ℕ}
    {A B : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {f : ι → E → E} {p : ι → E}
    (hA : ∀ i x, ContDiffAt ℝ ∞ (A i) x)
    (hB : ∀ i x, ContDiffAt ℝ ∞ (B i) x)
    (hAi : ∀ i x, (A i x).IsInvertible) (hBi : ∀ i x, (B i x).IsInvertible)
    (hBs : ∀ i x u v, B i x u v = B i x v u)
    (hf : ∀ i, ∀ᶠ x in 𝓝 (p i), ContDiffAt ℝ ∞ (f i) x)
    {a : ℝ} (ha : 0 < a)
    (hAlow : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (p i) v v)
    (hBlow : ∀ i v, a * ‖v‖ ^ 2 ≤ B i (f i (p i)) v v)
    (hAj : HasUniformJetBoundsAt (n + 1) A p)
    (hBj : HasUniformJetBoundsAt (n + 1) B (fun i => f i (p i)))
    (hzero : ∃ C : ℝ, ∀ i, ‖f i (p i)‖ ≤ C)
    (hmetric : ∀ i, ∀ᶠ x in 𝓝 (p i), ∀ u v,
      B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v) = A i x u v) :
    HasUniformJetBoundsAt (n + 2) f p := by
  let GA : ι → E → E →L[ℝ] E →L[ℝ] E :=
    fun i => CoordinateExponential.christoffelBilinear (A i)
  let GB : ι → E → E →L[ℝ] E →L[ℝ] E :=
    fun i => CoordinateExponential.christoffelBilinear (B i)
  obtain ⟨CA, hCA⟩ := hAj 0 (Nat.zero_le _)
  have hfirst : ∃ C : ℝ, ∀ i, ‖fderiv ℝ (f i) (p i)‖ ≤ C := by
    refine ⟨Real.sqrt (max CA 0 / a), fun i => ?_⟩
    apply norm_le_of_pullback_quadratic_bounds (A i (p i)) (B i (f i (p i)))
      (fderiv ℝ (f i) (p i)) ha (le_max_right _ _) (fun v => ?_)
      (hBlow i) (hmetric i).self_of_nhds
    have hnorm : ‖A i (p i)‖ ≤ max CA 0 :=
      (by simpa only [norm_iteratedFDeriv_zero] using hCA i : ‖A i (p i)‖ ≤ CA).trans
        (le_max_left _ _)
    calc
      A i (p i) v v ≤ ‖A i (p i) v v‖ := le_abs_self _
      _ ≤ ‖A i (p i)‖ * (‖v‖ * ‖v‖) := by
        simpa only [mul_assoc] using (A i (p i)).le_opNorm₂ v v
      _ ≤ max CA 0 * (‖v‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = max CA 0 * ‖v‖ ^ 2 := by rw [pow_two]
  have hGA : HasUniformJetBoundsAt n GA p :=
    finite_christoffel_jets_at (fun i => hA i (p i)) hAj ha hAlow
  have hGB : HasUniformJetBoundsAt n GB (fun i => f i (p i)) :=
    finite_christoffel_jets_at (fun i => hB i (f i (p i))) hBj ha hBlow
  have hsGA : ∀ i, ContDiffAt ℝ ∞ (GA i) (p i) :=
    fun i => CoordinateExponential.contDiffAt_christoffelBilinear (hA i (p i)) (hAi i (p i))
  have hsGB : ∀ i, ContDiffAt ℝ ∞ (GB i) (f i (p i)) :=
    fun i => CoordinateExponential.contDiffAt_christoffelBilinear
      (hB i (f i (p i))) (hBi i (f i (p i)))
  apply finite_jets_at_of_christoffel_hessian (fun i => (hf i).self_of_nhds)
    hsGA hsGB hGA hGB hzero hfirst
  intro i
  filter_upwards [hf i, (hmetric i).eventually_nhds] with x hfx hmetricx
  exact fderiv_fderiv_eq_transitionHessianPolynomial
    ((hA i x).differentiableAt (by simp)) ((hB i (f i x)).differentiableAt (by simp))
    (hAi i x) (hBi i (f i x)) (hBs i (f i x)) hfx
    (surjective_of_pullback_isInvertible (hAi i x)
      (fun u v => (hmetricx.self_of_nhds u v).symm))
    (hmetricx.mono (fun _ h u v => (h u v).symm))

end PoincareConjecture.M35
