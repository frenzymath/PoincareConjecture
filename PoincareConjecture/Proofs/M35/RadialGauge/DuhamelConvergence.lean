import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelDerivative
import PoincareConjecture.Proofs.M35.RadialGauge.SlabSourceExtension
import Mathlib.MeasureTheory.Integral.DominatedConvergence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem heatDuhamel_tendsto {f : ℕ → ℝ → V → F} {g : ℝ → V → F} {C t : ℝ}
    (ht : 0 ≤ t) (hfm : ∀ k, StronglyMeasurable (Function.uncurry (f k)))
    (hf : ∀ k s, s ∈ Icc 0 t → Continuous (f k s))
    (hbound : ∀ k s, s ∈ Icc 0 t → ∀ x, ‖f k s x‖ ≤ C)
    (hlim : ∀ s, s ∈ Icc 0 t → ∀ x, Tendsto (fun k => f k s x) atTop (𝓝 (g s x)))
    (x : V) :
    Tendsto (fun k => heatDuhamel (f k) t x) atTop (𝓝 (heatDuhamel g t x)) := by
  have hinner (s : ℝ) (hs : s ∈ Icc 0 t) :
      Tendsto (fun k => heatAverage (t - s) (f k s) x) atTop
        (𝓝 (heatAverage (t - s) (g s) x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro k
      exact ((hf k s hs).comp (by fun_prop)).aestronglyMeasurable
    · exact integrable_const C
    · intro k
      exact Eventually.of_forall (fun z => hbound k s hs _)
    · exact Eventually.of_forall (fun z => hlim s hs _)
  simp only [heatDuhamel, intervalIntegral.integral_of_le ht]
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro k
    exact (heatAverage_time_stronglyMeasurable (hfm k) t x).aestronglyMeasurable
  · exact integrable_const C
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simpa [heatAverage] using norm_integral_le_of_norm_le_const (μ := stdGaussian V)
      (Eventually.of_forall (fun z => hbound k s ⟨hs.1.le, hs.2⟩
        (x + Real.sqrt (2 * (t - s)) • z)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hinner s ⟨hs.1.le, hs.2⟩



theorem heatDuhamel_tendsto_on_slab {f : ℕ → ℝ → V → F} {g : ℝ → V → F}
    {C T t : ℝ} (ht : t ∈ Icc 0 T)
    (hfm : ∀ k, StronglyMeasurable (fun p : Icc (0 : ℝ) T × V => f k p.1 p.2))
    (hf : ∀ k s, s ∈ Icc 0 T → Continuous (f k s))
    (hbound : ∀ k s, s ∈ Icc 0 T → ∀ x, ‖f k s x‖ ≤ C)
    (hlim : ∀ s, s ∈ Icc 0 T → ∀ x, Tendsto (fun k => f k s x) atTop (𝓝 (g s x)))
    (x : V) :
    Tendsto (fun k => heatDuhamel (f k) t x) atTop (𝓝 (heatDuhamel g t x)) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have h := heatDuhamel_tendsto (g := slabSourceExtension T g) (C := C) ht.1
    (fun k => slabSourceExtension_stronglyMeasurable (hfm k))
    (fun k s hs => by rw [slabSourceExtension_of_mem (hsub hs)]; exact hf k s (hsub hs))
    (fun k s hs x => by rw [slabSourceExtension_of_mem (hsub hs)]; exact hbound k s (hsub hs) x)
    (fun s hs x => by
      simpa only [slabSourceExtension_of_mem (hsub hs)] using hlim s (hsub hs) x) x
  simpa only [heatDuhamel_slabSourceExtension ht] using h

end PoincareConjecture.M35.RadialGauge
