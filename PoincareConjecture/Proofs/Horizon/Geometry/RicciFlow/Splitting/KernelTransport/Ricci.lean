import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.NullSections
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.KernelTransport.Monotonicity
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open Poincare.RicciFlow.Splitting LeviCivitaData

private lemma differentiableWithinAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {S : Set ℝ} {t : ℝ}
    (hf : ∀ v, DifferentiableWithinAt ℝ (fun s => f s v) S t) :
    DifferentiableWithinAt ℝ f S t := by
  let d := Module.finrank ℝ E
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.differentiableAt.comp_differentiableWithinAt t
    (differentiableWithinAt_pi.mpr fun i => hf _)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

lemma coordinateRicciOperator_differentiableWithinAt
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Icc a b))
    (p x : M) {t : ℝ} (ht : t ∈ Icc a b) :
    DifferentiableWithinAt ℝ
      (fun s => coordinateRicciOperator (F.connection s) p x) (Icc a b) t := by
  have hB : DifferentiableWithinAt ℝ
      (fun s => coordinateRicciBilinear (F.connection s) p x) (Icc a b) t := by
    apply differentiableWithinAt_clm_of_apply
    intro v
    apply differentiableWithinAt_clm_of_apply
    intro w
    simpa only [coordinateRicciBilinear_apply] using
      (hC.ricci_evolution n M (Icc a b) F t ht x
        (constantCoordinateField p v x) (constantCoordinateField p w x)).differentiableWithinAt
  exact (differentiableWithinAt_const _).clm_comp hB

theorem ricciKernel_antitone_of_derivative_annihilates
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Icc a b)) (x : M)
    (hdim : AntitoneOn (fun t => ricciNullity (F.connection t) x) (Icc a b))
    (hann : ∀ t ∈ Ioc a b, ∀ v : TangentSpace (𝓡 n) x,
      (∀ w, (F.connection t).ricci x v w = 0) →
      ∀ w, HasDerivWithinAt (fun s => (F.connection s).ricci x v w) 0 (Icc a b) t) :
    AntitoneOn (fun t => ricciKernel (F.connection t) x) (Icc a b) := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace (𝓡 n)) x
  let A := fun r => coordinateRicciOperator (F.connection r) x x
  have hA (r : ℝ) (hr : r ∈ Icc a b) : DifferentiableWithinAt ℝ A (Icc a b) r :=
    coordinateRicciOperator_differentiableWithinAt hC F x x hr
  have hsym (r : ℝ) : (A r).toLinearMap.IsSymmetric := by
    intro v w
    change inner ℝ (A r v) w = inner ℝ v (A r w)
    conv_rhs => rw [real_inner_comm]
    rw [coordinateRicciOperator_inner, coordinateRicciOperator_inner]
    exact ((hC.tensor_calculus n M (F.metric r) (F.connection r)).2.2.2.1 x _ _ 0 0).2.2.2
  have hkernel {c d : ℝ} (hc : a < c) (hd : d ≤ b) (hcd : c < d) :
      AntitoneOn (fun r => (A r).ker) (Icc c d) := by
    have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hc.le hd
    let dA := fun r => derivWithin A (Icc c d) r
    have hAd (r : ℝ) (hr : r ∈ Icc c d) :
        HasDerivWithinAt A (dA r) (Icc c d) r :=
      ((hA r (hsub hr)).mono hsub).hasDerivWithinAt
    apply kernel_antitone_of_derivative_annihilates hAd (fun r _ => hsym r)
    · intro r hr s hs hrs
      change Module.finrank ℝ (coordinateRicciOperator (F.connection s) x x).ker ≤
        Module.finrank ℝ (coordinateRicciOperator (F.connection r) x x).ker
      rw [coordinateRicciOperator_finrank_ker _ x hx,
        coordinateRicciOperator_finrank_ker _ x hx]
      exact hdim (hsub hr) (hsub hs) hrs
    · intro r hr v hv
      apply ext_inner_right ℝ
      intro w
      have hnull := (coordinateRicciOperator_eq_zero_iff (F.connection r) x hx v).mp hv
      have hz := (hann r ⟨hc.trans_le hr.1, hr.2.trans hd⟩
        (constantCoordinateField x v x) hnull (constantCoordinateField x w x)).mono hsub
      have hp := ((hAd r hr).clm_apply (hasDerivWithinAt_const r (Icc c d) v)).inner ℝ
        (hasDerivWithinAt_const r (Icc c d) w)
      have hz' : HasDerivWithinAt (fun s => inner ℝ (A s v) w) 0 (Icc c d) r := by
        simpa only [A, coordinateRicciOperator_inner] using hz
      have heq := (hp.derivWithin (uniqueDiffOn_Icc hcd r hr)).symm.trans
        (hz'.derivWithin (uniqueDiffOn_Icc hcd r hr))
      simpa only [inner_add_left, map_zero, inner_zero_left, inner_zero_right,
        add_zero, zero_add] using heq
  intro s hs t ht hst v hv
  rw [mem_ricciKernel] at hv ⊢
  by_cases hst' : s = t
  · rw [hst']
    exact hv
  have hstlt : s < t := lt_of_le_of_ne hst hst'
  have hat : a < t := hs.1.trans_lt hstlt
  have hbefore (r : ℝ) (hr : r ∈ Ioc a t) : ∀ w, (F.connection r).ricci x v w = 0 := by
    by_cases hrt : r = t
    · rw [hrt]
      exact hv
    have hrt' : r < t := lt_of_le_of_ne hr.2 hrt
    let v₀ := e.continuousLinearMapAt ℝ x v
    have hv₀ : A t v₀ = 0 := by
      apply (coordinateRicciOperator_eq_zero_iff (F.connection t) x hx v₀).mpr
      change ∀ w, (F.connection t).ricci x (e.symmL ℝ x (e.continuousLinearMapAt ℝ x v)) w = 0
      rw [e.symmL_continuousLinearMapAt hx]
      exact hv
    have hrv := hkernel hr.1 ht.2 hrt' (left_mem_Icc.mpr hr.2) (right_mem_Icc.mpr hr.2) hr.2 hv₀
    have h := (coordinateRicciOperator_eq_zero_iff (F.connection r) x hx v₀).mp hrv
    change ∀ w, (F.connection r).ricci x (e.symmL ℝ x (e.continuousLinearMapAt ℝ x v)) w = 0 at h
    rwa [e.symmL_continuousLinearMapAt hx] at h
  intro w
  have heq : EqOn (fun r => (F.connection r).ricci x v w) (fun _ => 0) (Ioc a t) :=
    fun r hr => hbefore r hr w
  apply heq.of_subset_closure _ continuousOn_const Ioc_subset_Icc_self
    (by rw [closure_Ioc hat.ne]) ⟨hs.1, hst⟩
  intro r hr
  exact ((hC.ricci_evolution n M (Icc a b) F r
    ⟨hr.1, hr.2.trans ht.2⟩ x v w).continuousWithinAt).mono (Icc_subset_Icc_right ht.2)

end PoincareConjecture.RicciFlow.Splitting
