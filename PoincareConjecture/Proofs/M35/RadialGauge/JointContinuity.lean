import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelJets
import PoincareConjecture.Proofs.M35.RadialGauge.HeatTimeDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem heatAverage_joint_continuous {f : V → F} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun p : ℝ × V => heatAverage p.1 f p.2) := by
  apply continuous_of_dominated (bound := fun _ : V => C)
  · intro p
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro p
    exact Eventually.of_forall (fun z => hbound _)
  · exact integrable_const C
  · exact Eventually.of_forall (fun z => hf.comp (by fun_prop))

theorem heatDuhamel_joint_continuous {f : ℝ → V → F} {C : ℝ}
    (hm : StronglyMeasurable (Function.uncurry f))
    (hc : ∀ s, Continuous (f s)) (hb : ∀ s x, ‖f s x‖ ≤ C) :
    Continuous (fun p : ℝ × V => heatDuhamel f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let H (q : ℝ × V) (s : ℝ) := heatAverage (q.1 - s) (f s) q.2
  have hcont (s : ℝ) : Continuous (fun q => H q s) := by
    exact (heatAverage_joint_continuous (hc s) (hb s)).comp
      (show Continuous (fun q : ℝ × V => (q.1 - s, q.2)) by fun_prop)
  have h := intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (μ := volume) (F := H) (fun _ => C) (min 0 p.1 - 1) (max 0 p.1 + 1)
    (a₀ := 0) (b₀ := p.1) (x₀ := p)
    (fun q => (heatAverage_time_stronglyMeasurable hm q.1 q.2).aestronglyMeasurable)
    (Eventually.of_forall (fun q => Eventually.of_forall (fun s =>
      heatAverage_norm_le (hc s) (hb s) (q.1 - s) q.2)))
    intervalIntegrable_const (Eventually.of_forall (fun s => (hcont s).continuousAt))
    (by constructor <;> linarith [min_le_left (0 : ℝ) p.1, le_max_left (0 : ℝ) p.1])
    (by constructor <;> linarith [min_le_right (0 : ℝ) p.1, le_max_right (0 : ℝ) p.1])
    (measure_singleton p.1)
  exact h.comp (f := fun q : ℝ × V => (q, q.1)) (by fun_prop)

theorem heatDuhamel_fderiv_slab_continuous {f : ℝ → V → F} {T C D : ℝ}
    (hm : StronglyMeasurable (fun p : Icc 0 T × V => f p.1.1 p.2))
    (hc : ∀ s ∈ Icc 0 T, ContDiff ℝ 1 (f s))
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖f s x‖ ≤ C)
    (hdb : ∀ s ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (f s) x‖ ≤ D) :
    Continuous (fun p : Icc 0 T × V => fderiv ℝ (heatDuhamel f p.1.1) p.2) := by
  let g := slabSourceExtension T f
  have hgm : StronglyMeasurable (Function.uncurry g) :=
    slabSourceExtension_stronglyMeasurable hm
  have hgc (s : ℝ) : ContDiff ℝ 1 (g s) := by
    by_cases hs : s ∈ Icc 0 T
    · rw [show g s = f s from slabSourceExtension_of_mem hs f]
      exact hc s hs
    · have heq : g s = fun _ => (0 : F) := by
        funext x
        simp only [g, slabSourceExtension, if_neg hs]
      rw [heq]
      exact contDiff_const
  have hdm := spatial_fderiv_stronglyMeasurable hgm
    (fun s => (hgc s).differentiable (by norm_num))
  have hdeq : (fun s => fderiv ℝ (g s)) =
      slabSourceExtension T (fun s => fderiv ℝ (f s)) := fderiv_slabSourceExtension T f
  have hdb' (s : ℝ) (x : V) : ‖fderiv ℝ (g s) x‖ ≤ max D 0 := by
    change ‖(fun s => fderiv ℝ (g s)) s x‖ ≤ _
    rw [hdeq]
    by_cases hs : s ∈ Icc 0 T
    · rw [slabSourceExtension_of_mem hs]
      exact (hdb s hs x).trans (le_max_left _ _)
    · simpa only [slabSourceExtension, if_neg hs, norm_zero] using le_max_right D 0
  have h := heatDuhamel_joint_continuous hdm
    (fun s => (hgc s).continuous_fderiv (by norm_num)) hdb'
  have h' := h.comp (show Continuous (fun p : Icc 0 T × V => (p.1.1, p.2)) by fun_prop)
  apply h'.congr
  intro p
  have hcomm := heatDuhamel_fderiv_commutes p.1.2.1 hgm hdm
    (fun s _ => hgc s) (C := C) (D := D)
    (fun s hs x => by
      rw [show g s = f s from slabSourceExtension_of_mem ⟨hs.1, hs.2.trans p.1.2.2⟩ f]
      exact hb s ⟨hs.1, hs.2.trans p.1.2.2⟩ x)
    (fun s hs x => by
      rw [show g s = f s from slabSourceExtension_of_mem ⟨hs.1, hs.2.trans p.1.2.2⟩ f]
      exact hdb s ⟨hs.1, hs.2.trans p.1.2.2⟩ x)
  dsimp only [Function.comp_def]
  rw [← hcomm, show heatDuhamel g p.1.1 = heatDuhamel f p.1.1 from
    heatDuhamel_slabSourceExtension p.1.2 f]

theorem heatDuhamel_slab_continuous {f : ℝ → V → F} {T C : ℝ}
    (hm : StronglyMeasurable (fun p : Icc 0 T × V => f p.1.1 p.2))
    (hc : ∀ s ∈ Icc 0 T, Continuous (f s))
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖f s x‖ ≤ C) :
    Continuous (fun p : Icc 0 T × V => heatDuhamel f p.1.1 p.2) := by
  let g := slabSourceExtension T f
  have hgc (s : ℝ) : Continuous (g s) := by
    by_cases hs : s ∈ Icc 0 T
    · rw [show g s = f s from slabSourceExtension_of_mem hs f]
      exact hc s hs
    · have heq : g s = fun _ => (0 : F) := by
        funext x
        simp only [g, slabSourceExtension, if_neg hs]
      rw [heq]
      exact continuous_const
  have hgb (s : ℝ) (x : V) : ‖g s x‖ ≤ max C 0 := by
    by_cases hs : s ∈ Icc 0 T
    · rw [show g s = f s from slabSourceExtension_of_mem hs f]
      exact (hb s hs x).trans (le_max_left _ _)
    · simpa only [g, slabSourceExtension, if_neg hs, norm_zero] using le_max_right C 0
  have h := heatDuhamel_joint_continuous (slabSourceExtension_stronglyMeasurable hm) hgc hgb
  have h' := h.comp (show Continuous (fun p : Icc 0 T × V => (p.1.1, p.2)) by fun_prop)
  simpa only [Function.comp_def, g,
    heatDuhamel_slabSourceExtension (Subtype.property _)] using h'

end PoincareConjecture.M35.RadialGauge
