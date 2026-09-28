import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Transport
import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.LowerBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jacobiCurvature (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x v : E) : E →L[ℝ] E :=
  let Γ := christoffelBilinear B
  ((fderiv ℝ Γ x).flip v).flip v - (fderiv ℝ Γ x v).flip v +
    (Γ x).flip (Γ x v v) - (Γ x v).comp ((Γ x).flip v)

theorem jacobiCurvature_apply
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hΓ : DifferentiableAt ℝ (christoffelBilinear B) x) (u v : E) :
    jacobiCurvature B x v u = coordinateCurvature B x u v v := by
  rw [coordinateCurvature_eq_christoffelCurvature hΓ]
  rfl

def parallelJacobiCoefficient (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (q : ℝ → E) (P : ℝ → E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  (P t).inverse.comp ((jacobiCurvature B (q t) (deriv q t)).comp (P t))

set_option maxSynthPendingDepth 8 in

theorem contDiffAt_jacobiCurvature [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : E}
    (hB : ContDiffAt ℝ ∞ B x) (hinv : (B x).IsInvertible) :
    ContDiffAt ℝ ∞ (fun p : E × E => jacobiCurvature B p.1 p.2) (x, v) := by
  have hΓ := contDiffAt_christoffelBilinear hB hinv
  have hd := hΓ.fderiv_right (m := ∞) (by simp)
  have hg : ContDiffAt ℝ ∞ (fun p : E × E => christoffelBilinear B p.1) (x, v) :=
    hΓ.comp (x, v) contDiffAt_fst
  have hdg : ContDiffAt ℝ ∞ (fun p : E × E => fderiv ℝ (christoffelBilinear B) p.1)
      (x, v) := hd.comp (x, v) contDiffAt_fst
  have hf : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] E => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).contDiff
  have hf' : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] E => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] E)).contDiff
  unfold jacobiCurvature
  fun_prop

theorem contDiffOn_parallelJacobiCoefficient [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {I T : Set ℝ}
    {q : ℝ → E} {P : ℝ → E →L[ℝ] E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hI : IsOpen I) (hq : ContDiffOn ℝ ∞ q I)
    (hmem : MapsTo q I U) (hsub : T ⊆ I)
    (hP : ContDiffOn ℝ ∞ P T) (hPi : ∀ t ∈ T, (P t).IsInvertible) :
    ContDiffOn ℝ ∞ (parallelJacobiCoefficient B q P) T := by
  intro t ht
  have hqt := hq.contDiffAt (hI.mem_nhds (hsub ht))
  have hdq : ContDiffAt ℝ ∞ (deriv q) t :=
    (hqt.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hC := (contDiffAt_jacobiCurvature
    (hB.contDiffAt (hU.mem_nhds (hmem (hsub ht))))
    (hinv _ (hmem (hsub ht)))).comp t (hqt.prodMk hdq)
  have hi : ContDiffWithinAt ℝ ∞ (fun s => (P s).inverse) T t :=
    (hPi t ht).contDiffAt_map_inverse.comp_contDiffWithinAt t (hP t ht)
  exact hi.clm_comp (hC.contDiffWithinAt.clm_comp (hP t ht))

theorem inverse_parallel_hasDerivWithinAt [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q J : ℝ → E}
    {P : ℝ → E →L[ℝ] E} {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hP : HasDerivWithinAt P
      ((ConnectionAlongCurve.parallelCoefficient B q t).comp (P t)) (Icc a b) t)
    (hinv : ∀ s ∈ Icc a b, (P s).IsInvertible)
    (hJ : DifferentiableAt ℝ J t) :
    HasDerivWithinAt (fun s => (P s).inverse (J s))
      ((P t).inverse (alongCovariantDerivative B q J t)) (Icc a b) t := by
  have h := ConnectionAlongCurve.hasDerivWithinAt_inverse_apply ht
    (uniqueDiffOn_Icc hab t ht) hP hinv hJ.hasDerivAt.hasDerivWithinAt
  simpa only [alongCovariantDerivative, ConnectionAlongCurve.parallelCoefficient,
    neg_apply, christoffelBilinear_apply, sub_neg_eq_add,
    fderiv_eq_smul_deriv, one_smul] using h

theorem isJacobiSolOn_inverse_parallel [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q J : ℝ → E}
    {P : ℝ → E →L[ℝ] E} {a b : ℝ} (hab : a < b)
    (hP : ∀ t ∈ Icc a b, HasDerivWithinAt P
      ((ConnectionAlongCurve.parallelCoefficient B q t).comp (P t)) (Icc a b) t)
    (hinv : ∀ t ∈ Icc a b, (P t).IsInvertible)
    (hJ : ∀ t ∈ Icc a b, DifferentiableAt ℝ J t)
    (hDJ : ∀ t ∈ Icc a b,
      DifferentiableAt ℝ (alongCovariantDerivative B q J) t)
    (hΓ : ∀ t ∈ Icc a b, DifferentiableAt ℝ (christoffelBilinear B) (q t))
    (hjac : ∀ t ∈ Icc a b,
      alongCovariantDerivative B q (alongCovariantDerivative B q J) t =
        -coordinateCurvature B (q t) (J t) (deriv q t) (deriv q t)) :
    Poincare.ODE.Jacobi.IsJacobiSolOn (parallelJacobiCoefficient B q P) a b
      (fun t => (P t).inverse (J t))
      (fun t => (P t).inverse (alongCovariantDerivative B q J t)) := by
  constructor
  · intro t ht
    exact inverse_parallel_hasDerivWithinAt hab ht (hP t ht) hinv (hJ t ht)
  · intro t ht
    have h := inverse_parallel_hasDerivWithinAt hab ht (hP t ht) hinv (hDJ t ht)
    simpa only [hjac t ht, map_neg, parallelJacobiCoefficient,
      ContinuousLinearMap.comp_apply, (hinv t ht).self_apply_inverse,
      jacobiCurvature_apply (hΓ t ht)] using h

theorem exists_parallel_jacobi_reduction [CompleteSpace E] [FiniteDimensional ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {I : Set ℝ} {q J : ℝ → E}
    {a b : ℝ} (hab : a < b)
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hsymm : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hI : IsOpen I) (hq : ContDiffOn ℝ ∞ q I) (hJ : ContDiffOn ℝ ∞ J I)
    (hmem : MapsTo q I U) (hsub : Icc a b ⊆ I)
    (hjac : ∀ t ∈ I,
      alongCovariantDerivative B q (alongCovariantDerivative B q J) t =
        -coordinateCurvature B (q t) (J t) (deriv q t) (deriv q t)) :
    ∃ P : ℝ → E →L[ℝ] E,
      P a = ContinuousLinearMap.id ℝ E ∧
      ContDiffOn ℝ ∞ P (Icc a b) ∧
      (∀ t ∈ Icc a b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt P
        ((ConnectionAlongCurve.parallelCoefficient B q t).comp (P t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ u v, B (q t) (P t u) (P t v) = B (q a) u v) ∧
      Poincare.ODE.Jacobi.IsJacobiSolOn (parallelJacobiCoefficient B q P) a b
        (fun t => (P t).inverse (J t))
        (fun t => (P t).inverse (alongCovariantDerivative B q J t)) := by
  obtain ⟨P, hPa, hPs, hPi, hP, hpair⟩ := ConnectionAlongCurve.exists_parallel_transport
    hab hU hB hinv hsymm hI hq hmem hsub
  refine ⟨P, hPa, hPs, hPi, hP, hpair, ?_⟩
  have hΓ (t) (ht : t ∈ I) : ContDiffAt ℝ ∞ (christoffelBilinear B) (q t) :=
    contDiffAt_christoffelBilinear (hB.contDiffAt (hU.mem_nhds (hmem ht)))
      (hinv _ (hmem ht))
  apply isJacobiSolOn_inverse_parallel hab hP hPi
    (fun t ht => (hJ.contDiffAt (hI.mem_nhds (hsub ht))).differentiableAt (by simp))
  · intro t ht
    have hc := ConnectionVariation.contDiffAt_covDerivAlong (hΓ t (hsub ht))
      (hq.contDiffAt (hI.mem_nhds (hsub ht)))
      (hJ.contDiffAt (hI.mem_nhds (hsub ht))) (1 : ℝ)
    have heq : ConnectionVariation.covDerivAlong (christoffelBilinear B) q J 1 =
        alongCovariantDerivative B q J := by
      funext s
      rfl
    rw [heq] at hc
    exact hc.differentiableAt (by simp)
  · exact fun t ht => (hΓ t (hsub ht)).differentiableAt (by simp)
  · exact fun t ht => hjac t (hsub ht)

end PoincareConjecture.CoordinateExponential
