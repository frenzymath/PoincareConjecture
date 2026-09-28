import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.SegmentDynamics
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawOperatorSmooth









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {W V H : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def equivalentHeatGenerator (I : V →L[ℝ] H) (e : W ≃L[ℝ] V)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H) (t : ℝ) : W →L[ℝ] W :=
  e.toContinuousLinearMap.adjoint.comp
    (((I.adjoint.comp (L t)) - P t).comp e.toContinuousLinearMap)

theorem equivalentHeatGenerator_pairing (I : V →L[ℝ] H) (e : W ≃L[ℝ] V)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H) (t : ℝ) (w u : W) :
    inner ℝ w (equivalentHeatGenerator I e P L t u) =
      inner ℝ (I (e w)) (L t (e u)) - inner ℝ (e w) (P t (e u)) := by
  simp only [equivalentHeatGenerator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, sub_apply, inner_sub_right,
    ContinuousLinearEquiv.coe_coe]

theorem contDiffOn_equivalentHeatGenerator (I : V →L[ℝ] H) (e : W ≃L[ℝ] V)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H) {S : Set ℝ}
    (hP : ContDiffOn ℝ ∞ P S) (hL : ContDiffOn ℝ ∞ L S) :
    ContDiffOn ℝ ∞ (equivalentHeatGenerator I e P L) S :=
  contDiffOn_const.clm_comp
    (((contDiffOn_const.clm_comp hL).sub hP).clm_comp contDiffOn_const)

theorem equivalentHeatGenerator_normalized (I : V →L[ℝ] H) (e : W ≃L[ℝ] V)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H)
    (hbase : ∀ w u : W, inner ℝ w u =
      inner ℝ (I (e w)) (I (e u)) + inner ℝ (e w) (P 0 (e u))) (t : ℝ) :
    equivalentHeatGenerator I e P L t =
      e.toContinuousLinearMap.adjoint.comp ((P 0 - P t).comp e.toContinuousLinearMap) +
      (I.comp e.toContinuousLinearMap).adjoint.comp ((L t).comp e.toContinuousLinearMap) -
      ContinuousLinearMap.id ℝ W +
      (I.comp e.toContinuousLinearMap).adjoint.comp (I.comp e.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro w
  simp only [equivalentHeatGenerator_pairing, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    inner_add_right, inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe]
  rw [hbase w u]
  ring

theorem equivalent_tested_integral_adjoint (I : V →L[ℝ] H) (e : W ≃L[ℝ] V)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H) {T : ℝ}
    (hP : ContinuousOn P (Icc 0 T)) (hL : ContinuousOn L (Icc 0 T))
    {v : ℝ → V} (hv : MemLp v 2 (timeMeasure T)) {U : ℝ → H}
    (heq : ∀ t ∈ Icc 0 T, ∀ w : V,
      inner ℝ (I w) (U t) = inner ℝ (I w) (U 0) +
        ∫ s in (0 : ℝ)..t, inner ℝ (I w) (L s (v s)) - inner ℝ w (P s (v s))) :
    ∀ t ∈ Icc 0 T, (I.comp e.toContinuousLinearMap).adjoint (U t) =
      (I.comp e.toContinuousLinearMap).adjoint (U 0) +
        ∫ s in (0 : ℝ)..t, equivalentHeatGenerator I e P L s (e.symm (v s)) := by
  have hAe : ContinuousOn (equivalentHeatGenerator I e P L) (Icc 0 T) :=
    continuousOn_const.clm_comp
      (((continuousOn_const.clm_comp hL).sub hP).clm_comp continuousOn_const)
  have hD := ValueInitial.memLp_continuous_operator _ hAe
    (e.symm.toContinuousLinearMap.comp_memLp' hv)
  apply ValueInitial.tested_integral_adjoint _ hD
  intro t ht w
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    equivalentHeatGenerator_pairing, Function.comp_def, e.apply_symm_apply] using heq t ht (e w)

end PoincareConjecture.M35.Uniqueness.Heat
