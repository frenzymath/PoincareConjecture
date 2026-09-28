import PoincareConjecture.Proofs.M35.RadialGauge.HeatTimeGain

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def slabSourceExtension (T : ℝ) (f : ℝ → V → F) (s : ℝ) (x : V) : F :=
  if s ∈ Icc 0 T then f s x else 0

omit [NormedSpace ℝ F] in

theorem slabSourceExtension_of_mem {T s : ℝ} (hs : s ∈ Icc 0 T)
    (f : ℝ → V → F) : slabSourceExtension T f s = f s := by
  funext x
  simp only [slabSourceExtension, if_pos hs]

omit [NormedSpace ℝ F] in

theorem slabSourceExtension_stronglyMeasurable {T : ℝ} {f : ℝ → V → F}
    (hf : StronglyMeasurable (fun p : Icc (0 : ℝ) T × V => f p.1.1 p.2)) :
    StronglyMeasurable (Function.uncurry (slabSourceExtension T f)) := by
  classical
  let S : Set (ℝ × V) := {p | p.1 ∈ Icc 0 T}
  have hS : MeasurableSet S := measurableSet_Icc.preimage measurable_fst
  have hbranch : StronglyMeasurable (fun p : S => f p.1.1 p.1.2) :=
    hf.comp_measurable
      (g := fun p : S => ((⟨p.1.1, p.2⟩ : Icc (0 : ℝ) T), p.1.2)) (by fun_prop)
  have h := hbranch.dite (g := fun _ : ↑(Sᶜ) => (0 : F)) stronglyMeasurable_const hS
  convert h using 1
  funext p
  dsimp only [Function.uncurry, slabSourceExtension, S]
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> rfl

theorem heatDuhamel_slabSourceExtension {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ → V → F) : heatDuhamel (slabSourceExtension T f) t = heatDuhamel f t := by
  funext x
  unfold heatDuhamel
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  change heatAverage (t - s) (slabSourceExtension T f s) x =
    heatAverage (t - s) (f s) x
  rw [slabSourceExtension_of_mem ⟨hs.1, hs.2.trans ht.2⟩]

theorem fderiv_heatDuhamel_slabSourceExtension {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ → V → F) :
    fderiv ℝ (heatDuhamel (slabSourceExtension T f) t) = fderiv ℝ (heatDuhamel f t) := by
  rw [heatDuhamel_slabSourceExtension ht]

theorem heatDuhamelGradient_slabSourceExtension {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ → V → F) :
    heatDuhamelGradient (slabSourceExtension T f) t = heatDuhamelGradient f t := by
  funext x
  unfold heatDuhamelGradient
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  change heatGradientKernel (t - s) (slabSourceExtension T f s) x =
    heatGradientKernel (t - s) (f s) x
  rw [slabSourceExtension_of_mem ⟨hs.1, hs.2.trans ht.2⟩]

end PoincareConjecture.M35.RadialGauge
