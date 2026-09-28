import PoincareConjecture.Proofs.M76.Mathlib.SimplexCoreBox
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open Set
open scoped ContDiff

namespace StdSimplexCore

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem contDiff_boxScale (ι : Type*) [Fintype ι] (η : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (boxScale ι η : (κ → ℝ) → ℝ) := by
  unfold boxScale
  fun_prop

theorem contDiff_boxPoint (ι κ : Type*) [Fintype ι] [Fintype κ] (η : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun z : (ι → ℝ) × (κ → ℝ) => boxPoint ι κ η z.1 z.2) := by
  unfold boxPoint
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    exact contDiff_const.add (((contDiff_boxScale ι η n).comp contDiff_snd).mul
      (((contDiff_apply ℝ ℝ i).comp contDiff_fst).sub contDiff_const))
  · exact contDiff_snd

theorem contDiffAt_boxBase (η : ℝ) (n : ℕ∞ω) (z : (ι → ℝ) × (κ → ℝ))
    (hz : boxScale ι η z.2 ≠ 0) : ContDiffAt ℝ n (boxBase ι κ η) z := by
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_const.add
    ((((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffAt.sub contDiffAt_const).div
      ((contDiff_boxScale ι η n).comp contDiff_snd).contDiffAt hz)

noncomputable def boxHomeomorph {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1) :
    (stdSimplexCore ι η × Icc (0 : κ → ℝ) (fun _ => η)) ≃ₜ boxRegion ι κ η where
  toFun z := ⟨boxPoint ι κ η z.1 z.2, boxPoint_mem hη hbound z.1.property z.2.property⟩
  invFun z := (⟨boxBase ι κ η z, boxBase_mem hη hbound z.property⟩,
    ⟨z.val.2, z.property.2.1⟩)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change boxBase ι κ η (boxPoint ι κ η z.1.val z.2.val) = z.1.val
      exact boxBase_boxPoint η z.1.val z.2.val
        (boxScale_pos (ι := ι) hη hbound z.2.property).ne'
    · rfl
  right_inv z := by
    apply Subtype.ext
    change boxPoint ι κ η (boxBase ι κ η z.val) z.val.2 = z.val
    exact boxPoint_boxBase η z.val (boxScale_pos (ι := ι) hη hbound z.property.2.1).ne'
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (contDiff_boxPoint ι κ η 0).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      rw [continuous_iff_continuousAt]
      intro z
      exact (contDiffAt_boxBase η 0 z.val
        (boxScale_pos (ι := ι) hη hbound z.property.2.1).ne').continuousAt.comp
          continuous_subtype_val.continuousAt
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _

noncomputable def boxExtension {Y : Type*} [TopologicalSpace Y] {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    (f : C(stdSimplexCore ι η, Y)) : C(boxRegion ι κ η, Y) :=
  f.comp ⟨fun z => ((boxHomeomorph hη hbound).symm z).1,
    continuous_fst.comp (boxHomeomorph hη hbound).symm.continuous⟩

theorem boxExtension_boxPoint {Y : Type*} [TopologicalSpace Y] {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    (f : C(stdSimplexCore ι η, Y)) (q : stdSimplexCore ι η)
    (v : Icc (0 : κ → ℝ) (fun _ => η)) :
    boxExtension hη hbound f ((boxHomeomorph hη hbound) (q, v)) = f q := by
  change f (((boxHomeomorph hη hbound).symm ((boxHomeomorph hη hbound) (q, v))).1) = f q
  rw [Homeomorph.symm_apply_apply]

end StdSimplexCore
