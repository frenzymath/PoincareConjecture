import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Compact.ClosedTimeExtension
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Paths.ClosedPathSubstitution
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Smooth substitution on paths in an open state domain

The actual closed-time field defines one smooth operator on all
continuous paths whose entire image stays in the state domain.
MT2007 Claim 19.1, p. 437, and Lemma 19.6, pp. 441-442;
`2026-09-22-closed-time-open-state-substitution.md`, statement 2.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

universe u v

namespace PoincareMT.M63

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal closed-time substitution is smooth in the path
variable on its actual open-state domain, in independent universes.
MT2007 Claim 19.1, p. 437; substitution derivation, statement 2. -/
theorem exists_contDiffOn_closedTime_pathSubstitution {C : Set ℝ} [CompactSpace C]
    (hC : UniqueDiffOn ℝ C) {U : Set E} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) :
    ∃ Phi : C(C, E) → C(C, F),
      ContDiffOn ℝ ∞ Phi {w | range w ⊆ U} ∧
      ∀ w : C(C, E), range w ⊆ U → ∀ t : C, Phi w t = f (t.val, w t) := by
  classical
  have hmap (w : C(C, E)) (hw : range w ⊆ U) :
      Continuous (fun t : C => f (t.val, w t)) :=
    hf.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk w.continuous)
      (fun t => ⟨t.property, hw ⟨t, rfl⟩⟩)
  let Phi : C(C, E) → C(C, F) := fun w =>
    if hw : range w ⊆ U then ⟨fun t => f (t.val, w t), hmap w hw⟩ else 0
  have hPhi (w : C(C, E)) (hw : range w ⊆ U) (t : C) :
      Phi w t = f (t.val, w t) := by
    simp only [Phi, dif_pos hw, ContinuousMap.coe_mk]
  refine ⟨Phi, ?_, hPhi⟩
  intro w hw
  obtain ⟨g, hg, O, hO, hwO, hOU, heq⟩ :=
    exists_closedTime_compact_state_extension (isCompact_range w.continuous) hU hw f hf
  let e : ULift.{v} E ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  let d : ULift.{u} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  let g' : ℝ × ULift.{v} E → ULift.{u} F := fun z => d.symm (g (z.1, e z.2))
  have hpair : ContDiff ℝ ∞ (fun z : ℝ × ULift.{v} E => (z.1, e z.2)) :=
    contDiff_fst.prodMk (e.contDiff.comp contDiff_snd)
  have hg' : ContDiffOn ℝ ∞ g' (C ×ˢ univ) :=
    d.symm.contDiff.comp_contDiffOn
      (hg.comp hpair.contDiffOn (fun z hz => ⟨hz.1, mem_univ _⟩))
  let up : C(C, E) →L[ℝ] C(C, ULift.{v} E) :=
    e.symm.toContinuousLinearMap.compLeftContinuous ℝ C
  let down : C(C, ULift.{u} F) →L[ℝ] C(C, F) :=
    d.toContinuousLinearMap.compLeftContinuous ℝ C
  let Psi : C(C, E) → C(C, F) := fun z =>
    down (M14.closedTimePostcomp g' hg'.continuousOn (up z))
  have hPsi : ContDiff ℝ ∞ Psi :=
    down.contDiff.comp ((M14.closedTimePostcomp_contDiff hC g' hg').comp up.contDiff)
  have hPsi_eval (z : C(C, E)) (t : C) : Psi z t = g (t.val, z t) := by
    change d (d.symm (g (t.val, e (e.symm (z t))))) = g (t.val, z t)
    rw [e.apply_symm_apply, d.apply_symm_apply]
  have hagree : Phi =ᶠ[𝓝 w] Psi := by
    filter_upwards [ContinuousMap.eventually_range_subset hO hwO] with z hz
    apply ContinuousMap.ext
    intro t
    rw [hPhi z (hz.trans hOU) t, hPsi_eval z t]
    exact (heq ⟨t.property, hz ⟨t, rfl⟩⟩).symm
  exact (hPsi.contDiffAt.congr_of_eventuallyEq hagree).contDiffWithinAt

end PoincareMT.M63
