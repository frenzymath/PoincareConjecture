import PoincareConjecture.Proofs.M07.Analysis.ODE.Linear
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Metric
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.ConnectionAlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem exists_invertible_solution {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) :
    ∃ P : ℝ → E →L[ℝ] E,
      P a = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt P ((A t).comp (P t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, (P t).IsInvertible) := by
  let C : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    fun t => ContinuousLinearMap.compL ℝ E E E (A t)
  have hC : ContinuousOn C (Icc a b) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := C) hC
  let K' : ℝ≥0 := ⟨max K 0, le_max_right _ _⟩
  have hK' : ∀ t ∈ Icc a b, ‖C t‖₊ ≤ K' := by
    intro t ht
    exact_mod_cast (hK t ht).trans (le_max_left K 0)
  obtain ⟨P, hPa, hP⟩ := Poincare.ODE.Linear.exists_hasDerivWithinAt_Icc
    hab C (ContinuousLinearMap.id ℝ E) hC hK'
  refine ⟨P, hPa, hP, ?_⟩
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := A) hA
  let L' : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  have hL' : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ L' := by
    intro t ht
    exact_mod_cast (hL t ht).trans (le_max_left L 0)
  intro t ht
  have hinj : Function.Injective (P t) := by
    intro v w hvw
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hsol (v : E) : Poincare.ODE.Linear.IsSolOn A a t (fun s => P s v) := by
      intro s hs
      simpa [C] using ((hP s (hsub hs)).mono hsub).clm_apply
        (hasDerivWithinAt_const s (Icc a t) v)
    have heq := Poincare.ODE.Linear.IsSolOn.eqOn_of_right
      (fun s hs => hL' s (hsub hs)) (hsol v) (hsol w) hvw
      (show a ∈ Icc a t from ⟨le_rfl, ht.1⟩)
    simpa [hPa] using heq
  have hbij : Function.Bijective (P t) :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (P t).toLinearMap)).mp hinj⟩
  exact ⟨(LinearEquiv.ofBijective (P t).toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

omit [FiniteDimensional ℝ E] in

theorem hasDerivWithinAt_inverse_apply
    {P : ℝ → E →L[ℝ] E} {A : E →L[ℝ] E} {J : ℝ → E} {J' : E}
    {S : Set ℝ} {t : ℝ} (ht : t ∈ S) (hS : UniqueDiffWithinAt ℝ S t)
    (hP : HasDerivWithinAt P (A.comp (P t)) S t)
    (hinv : ∀ s ∈ S, (P s).IsInvertible)
    (hJ : HasDerivWithinAt J J' S t) :
    HasDerivWithinAt (fun s => (P s).inverse (J s))
      ((P t).inverse (J' - A (J t))) S t := by
  let Y : ℝ → E := fun s => (P s).inverse (J s)
  have hi : DifferentiableWithinAt ℝ (fun s => (P s).inverse) S t :=
    ((hinv t ht).contDiffAt_map_inverse (n := 1)).differentiableAt (by norm_num)
      |>.comp_differentiableWithinAt t hP.differentiableWithinAt
  have hY : DifferentiableWithinAt ℝ Y S t := hi.clm_apply hJ.differentiableWithinAt
  have hd := hY.hasDerivWithinAt
  have hprod : HasDerivWithinAt (fun s => P s (Y s))
      (A (J t) + P t (derivWithin Y S t)) S t := by
    simpa only [ContinuousLinearMap.comp_apply, Y, (hinv t ht).self_apply_inverse]
      using hP.clm_apply hd
  have heq : HasDerivWithinAt J
      (A (J t) + P t (derivWithin Y S t)) S t :=
    hprod.congr (fun s hs => ((hinv s hs).self_apply_inverse (J s)).symm)
      ((hinv t ht).self_apply_inverse (J t)).symm
  have hval := (heq.derivWithin hS).symm.trans (hJ.derivWithin hS)
  have hv : P t (derivWithin Y S t) = J' - A (J t) := by
    rw [← hval]
    abel
  have hdval : derivWithin Y S t = (P t).inverse (J' - A (J t)) := by
    rw [← hv, (hinv t ht).inverse_apply_self]
  rwa [hdval] at hd

omit [FiniteDimensional ℝ E] [CompleteSpace E] in

theorem contDiffOn_solution {a b : ℝ} (hab : a < b)
    {A : ℝ → E →L[ℝ] E} {P : ℝ → E →L[ℝ] E}
    (hA : ContDiffOn ℝ ∞ A (Icc a b))
    (hP : ∀ t ∈ Icc a b, HasDerivWithinAt P ((A t).comp (P t)) (Icc a b) t) :
    ContDiffOn ℝ ∞ P (Icc a b) := by
  rw [contDiffOn_infty]
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr (fun t ht => (hP t ht).continuousWithinAt)
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
    refine ⟨fun t ht => (hP t ht).differentiableWithinAt, ?_, ?_⟩
    · simp
    · have hAk : ContDiffOn ℝ (k : ℕ∞ω) A (Icc a b) :=
        hA.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
      exact (hAk.clm_comp ih).congr (fun t ht =>
        (hP t ht).derivWithin (uniqueDiffOn_Icc hab t ht))

open CoordinateExponential

def parallelCoefficient (B : E → E →L[ℝ] E →L[ℝ] ℝ) (q : ℝ → E)
    (t : ℝ) : E →L[ℝ] E :=
  -christoffelBilinear B (q t) (deriv q t)

omit [FiniteDimensional ℝ E] in

theorem contDiffOn_parallelCoefficient
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {I : Set ℝ} {q : ℝ → E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hI : IsOpen I) (hq : ContDiffOn ℝ ∞ q I) (hmem : MapsTo q I U) :
    ContDiffOn ℝ ∞ (parallelCoefficient B q) I := by
  intro t ht
  have hqt := hq.contDiffAt (hI.mem_nhds ht)
  have hc := contDiffAt_christoffelBilinear
    (hB.contDiffAt (hU.mem_nhds (hmem ht))) (hinv _ (hmem ht))
  have hd : ContDiffAt ℝ ∞ (deriv q) t :=
    (hqt.fderiv_right (by simp)).clm_apply contDiffAt_const
  exact (((hc.comp t hqt).clm_apply hd).neg).contDiffWithinAt

theorem exists_parallel_transport
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {I : Set ℝ} {q : ℝ → E}
    {a b : ℝ} (hab : a < b)
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hsymm : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hI : IsOpen I) (hq : ContDiffOn ℝ ∞ q I)
    (hmem : MapsTo q I U) (hsub : Icc a b ⊆ I) :
    ∃ P : ℝ → E →L[ℝ] E,
      P a = ContinuousLinearMap.id ℝ E ∧
      ContDiffOn ℝ ∞ P (Icc a b) ∧
      (∀ t ∈ Icc a b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt P
        ((parallelCoefficient B q t).comp (P t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ u v, B (q t) (P t u) (P t v) = B (q a) u v) := by
  have hA := (contDiffOn_parallelCoefficient hU hB hinv hI hq hmem).mono hsub
  obtain ⟨P, hPa, hP, hPi⟩ := exists_invertible_solution hab.le _ hA.continuousOn
  refine ⟨P, hPa, contDiffOn_solution hab hA hP, hPi, hP, ?_⟩
  intro t ht u v
  let f := fun s => B (q s) (P s u) (P s v)
  have hd : ∀ s ∈ Icc a b, HasDerivWithinAt f 0 (Icc a b) s := by
    intro s hs
    have hq' := (hq.contDiffAt (hI.mem_nhds (hsub hs))).differentiableAt (by simp)
    have hx := hmem (hsub hs)
    apply hasDerivWithinAt_metric_parallel
      ((hB.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) (hinv _ hx)
      (Filter.Eventually.mono (hU.mem_nhds hx) (fun x hx => hsymm x hx)) hq'
    · simpa only [parallelCoefficient, ContinuousLinearMap.comp_apply,
        neg_apply, christoffelBilinear_apply, map_zero, add_zero]
        using (hP s hs).clm_apply (hasDerivWithinAt_const s (Icc a b) u)
    · simpa only [parallelCoefficient, ContinuousLinearMap.comp_apply,
        neg_apply, christoffelBilinear_apply, map_zero, add_zero]
        using (hP s hs).clm_apply (hasDerivWithinAt_const s (Icc a b) v)
  have heq := constant_of_derivWithin_zero
    (fun s hs => (hd s hs).differentiableWithinAt)
    (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hab s ⟨hs.1, hs.2.le⟩)) t ht
  simpa only [f, hPa, ContinuousLinearMap.id_apply] using heq

end PoincareConjecture.ConnectionAlongCurve
