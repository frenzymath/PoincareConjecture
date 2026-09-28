import PoincareConjecture.Proofs.M09.LocalFlowOn
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open scoped ContDiff Topology
open Set

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_local_smooth_timeDependent_flow (S : Set (ℝ × E)) (hS : IsOpen S)
    (f : ℝ × E → E) (hf : ContDiffOn ℝ ∞ f S) (z0 : ℝ × E) (hz0 : z0 ∈ S) :
    ∃ (beta : (ℝ × E) × ℝ → E) (V : Set (ℝ × E)) (d : ℝ),
      IsOpen V ∧ z0 ∈ V ∧ V ⊆ S ∧ 0 < d ∧
      ContDiffOn ℝ ∞ beta (V ×ˢ Set.Ioo (-d) d) ∧
      (∀ z ∈ V, beta (z, 0) = z.2) ∧
      ∀ z ∈ V, ∀ t ∈ Set.Ioo (-d) d,
        (z.1 + t, beta (z, t)) ∈ S ∧
        HasDerivAt (fun a ↦ beta (z, a)) (f (z.1 + t, beta (z, t))) t := by
  let A : ℝ × E → ℝ × E := fun z ↦ (1, f z)
  have hA : ContDiffOn ℝ ∞ A S := contDiffOn_const.prodMk hf
  obtain ⟨alpha, V, d, hV, hzV, hVS, hd, hasmooth, hainit, haode⟩ :=
    exists_local_smooth_flow_on S hS A hA z0 hz0
  let beta : (ℝ × E) × ℝ → E := fun z ↦ (alpha z).2
  have hzero : (0 : ℝ) ∈ Set.Ioo (-d) d := by constructor <;> linarith
  have htime : ∀ z ∈ V, ∀ t ∈ Set.Ioo (-d) d, (alpha (z, t)).1 = z.1 + t := by
    intro z hz
    have hfirst : ∀ t ∈ Set.Ioo (-d) d,
        HasDerivAt (fun a ↦ (alpha (z, a)).1) 1 t := by
      intro t ht
      exact hasFDerivAt_fst.comp_hasDerivAt t (haode z hz t ht).2
    have hlinear (t : ℝ) : HasDerivAt (fun a : ℝ ↦ z.1 + a) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t).const_add z.1
    have hsame : Set.EqOn (fun t ↦ (alpha (z, t)).1) (fun t ↦ z.1 + t)
        (Set.Ioo (-d) d) :=
      isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
        (fun t ht ↦ (hfirst t ht).differentiableAt.differentiableWithinAt)
        (fun t _ ↦ (hlinear t).differentiableAt.differentiableWithinAt)
        (fun t ht ↦ (hfirst t ht).deriv.trans (hlinear t).deriv.symm) hzero
        (by simpa only [add_zero] using congrArg Prod.fst (hainit z hz))
    exact fun t ht ↦ hsame ht
  refine ⟨beta, V, d, hV, hzV, hVS, hd, contDiff_snd.comp_contDiffOn hasmooth, ?_, ?_⟩
  · intro z hz
    exact congrArg Prod.snd (hainit z hz)
  · intro z hz t ht
    have hpair : alpha (z, t) = (z.1 + t, beta (z, t)) := by
      apply Prod.ext
      · exact htime z hz t ht
      · rfl
    refine ⟨hpair ▸ (haode z hz t ht).1, ?_⟩
    have hder : HasDerivAt (fun a ↦ beta (z, a)) (f (alpha (z, t))) t :=
      (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := E)).comp_hasDerivAt t
        (haode z hz t ht).2
    rwa [hpair] at hder

end PoincareConjecture.Proofs.M09
