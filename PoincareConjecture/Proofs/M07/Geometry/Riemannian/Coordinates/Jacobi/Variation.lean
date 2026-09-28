import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ParallelFrame
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem GeodesicVariation.contDiffOn_variationField
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {S I : Set ℝ}
    (Γ : GeodesicVariation B S I) (hS : IsOpen S) (hI : IsOpen I) :
    ContDiffOn ℝ ∞ (variationField Γ) I := by
  let u : ℝ × ℝ → E := fun p => (Γ.phase p).1
  let F : ℝ → E := fun t => fderiv ℝ u (0, t) (1, 0)
  have heq (t : ℝ) (ht : t ∈ I) : F t = variationField Γ t := by
    have hus : ContDiffAt ℝ ∞ u (0, t) := (Γ.smooth.contDiffAt
      ((hS.prod hI).mem_nhds (show (0, t) ∈ S ×ˢ I from ⟨Γ.base_mem, ht⟩))).fst
    have hu := hus.differentiableAt (by simp)
    have hc : HasDerivAt (fun s : ℝ => (s, t)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 t)
    have hd := hu.hasFDerivAt.comp_hasDerivAt 0 hc
    simpa only [F, variationField, fderiv_eq_smul_deriv, one_smul,
      Function.comp_def, u] using hd.deriv.symm
  intro t ht
  have hu : ContDiffAt ℝ ∞ u (0, t) :=
    (Γ.smooth.contDiffAt ((hS.prod hI).mem_nhds ⟨Γ.base_mem, ht⟩)).fst
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => ((0 : ℝ), t)) t :=
    contDiffAt_const.prodMk contDiffAt_id
  have hF : ContDiffAt ℝ ∞ F t :=
    (((hu.fderiv_right (by simp)).comp t hc).clm_apply contDiffAt_const)
  exact hF.contDiffWithinAt.congr (fun s hs => (heq s hs).symm) (heq t ht).symm


theorem GeodesicVariation.deriv_position
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {S I : Set ℝ}
    (Γ : GeodesicVariation B S I) {t : ℝ} (ht : t ∈ I) :
    deriv (fun s => (Γ.phase (0, s)).1) t = (Γ.phase (0, t)).2 := by
  have hd : HasDerivAt (fun s => (Γ.phase (0, s)).1) (Γ.phase (0, t)).2 t :=
    (Γ.geodesic 0 Γ.base_mem t ht).fst
  exact hd.deriv



theorem GeodesicVariation.exists_parallel_jacobi [CompleteSpace E] [FiniteDimensional ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {S I : Set ℝ} {a b : ℝ}
    (Γ : GeodesicVariation B S I) (hab : a < b)
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hsymm : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    (hS : IsOpen S) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hmem : ∀ s ∈ S, ∀ t ∈ I, (Γ.phase (s, t)).1 ∈ U) :
    ∃ P : ℝ → E →L[ℝ] E,
      P a = ContinuousLinearMap.id ℝ E ∧
      ContDiffOn ℝ ∞ P (Icc a b) ∧
      (∀ t ∈ Icc a b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt P
        ((ConnectionAlongCurve.parallelCoefficient B (fun s => (Γ.phase (0, s)).1) t).comp
          (P t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ u v, B (Γ.phase (0, t)).1 (P t u) (P t v) =
        B (Γ.phase (0, a)).1 u v) ∧
      Poincare.ODE.Jacobi.IsJacobiSolOn
        (parallelJacobiCoefficient B (fun s => (Γ.phase (0, s)).1) P) a b
        (fun t => (P t).inverse (variationField Γ t))
        (fun t => (P t).inverse
          (alongCovariantDerivative B (fun s => (Γ.phase (0, s)).1) (variationField Γ) t)) := by
  have hq : ContDiffOn ℝ ∞ (fun s => (Γ.phase (0, s)).1) I := by
    intro t ht
    exact (((Γ.smooth.contDiffAt ((hS.prod hI).mem_nhds ⟨Γ.base_mem, ht⟩)).fst).comp t
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  apply exists_parallel_jacobi_reduction hab hU hB hinv hsymm hI hq
    (Γ.contDiffOn_variationField hS hI) (fun t ht => hmem 0 Γ.base_mem t ht) hsub
  intro t ht
  rw [Γ.deriv_position ht]
  exact eq_neg_of_add_eq_zero_left
    (geodesicVariation_jacobi hU hB hinv hsymm hS hI Γ.base_mem Γ hmem t ht)

end PoincareConjecture.CoordinateExponential
