import PoincareConjecture.Proofs.M35.RadialGauge.TimeSmoothness
import PoincareConjecture.Proofs.M35.RadialGauge.SlabSourceExtension
import PoincareConjecture.Proofs.M35.RadialGauge.HeatC1Bounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))


theorem fderiv_slabSourceExtension (T : ℝ) (f : ℝ → V → F) :
    (fun s => fderiv ℝ (slabSourceExtension T f s)) =
      slabSourceExtension T (fun s => fderiv ℝ (f s)) := by
  funext s
  by_cases hs : s ∈ Icc 0 T
  · rw [slabSourceExtension_of_mem hs, slabSourceExtension_of_mem hs]
  · have hzero : slabSourceExtension T f s = fun _ => (0 : F) := by
      funext x
      simp only [slabSourceExtension, if_neg hs]
    rw [hzero]
    funext x
    simp only [fderiv_const_apply, slabSourceExtension, if_neg hs]



theorem heatDuhamel_fderiv_commutes
    {f : ℝ → V → F} {t C D : ℝ} (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hdfm : StronglyMeasurable (fun p : ℝ × V => fderiv ℝ (f p.1) p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (f s))
    (hC : ∀ s ∈ Icc 0 t, ∀ x, ‖f s x‖ ≤ C)
    (hD : ∀ s ∈ Icc 0 t, ∀ x, ‖fderiv ℝ (f s) x‖ ≤ D) :
    fderiv ℝ (heatDuhamel f t) = heatDuhamel (fun s => fderiv ℝ (f s)) t := by
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (uIoc 0 t)) := by
    rw [uIoc_of_le ht]
    infer_instance
  have hs : ∀ᵐ s ∂volume.restrict (uIoc 0 t), s ∈ Icc 0 t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le ht] at hs
    exact ⟨hs.1.le, hs.2⟩
  have hderiv (x : V) : HasFDerivAt (heatDuhamel f t)
      (heatDuhamel (fun s => fderiv ℝ (f s)) t x) x := by
    unfold heatDuhamel
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (s := univ) (F' := fun y s => heatAverage (t - s) (fderiv ℝ (f s)) y)
      (bound := fun _ => D) (by simp)
    · exact Eventually.of_forall (fun y =>
        (heatAverage_time_stronglyMeasurable hfm t y).aestronglyMeasurable)
    · rw [intervalIntegrable_iff]
      apply (integrable_const C).mono'
        (heatAverage_time_stronglyMeasurable hfm t x).aestronglyMeasurable
      filter_upwards [hs] with s hs
      exact heatAverage_norm_le (hf s hs).continuous (hC s hs) (t - s) x
    · exact (heatAverage_time_stronglyMeasurable hdfm t x).aestronglyMeasurable
    · filter_upwards [hs] with s hs y _
      exact heatAverage_norm_le ((hf s hs).continuous_fderiv (by norm_num))
        (hD s hs) (t - s) y
    · exact intervalIntegrable_const
    · filter_upwards [hs] with s hs y _
      exact heatAverage_hasFDerivAt_of_bounds (hf s hs).continuous
        ((hf s hs).continuous_fderiv (by norm_num))
        (fun z => ((hf s hs).differentiable (by norm_num) z).hasFDerivAt)
        (hC s hs) (hD s hs) (t - s) y
  funext x
  exact (hderiv x).fderiv




theorem heatDuhamel_weighted_hessian_bound
    {f : ℝ → V → F} {t C : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hfm : StronglyMeasurable (fun p : Icc 0 t × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s))
    (hbound : ∀ k : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ k (f s) x‖ ≤ B)
    (hdf : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (f s) x‖ ≤ C)
    (x : V) :
    (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x‖ ≤
      C * heatC1Gain (n + 1) t := by
  let g := slabSourceExtension t f
  have hgm : StronglyMeasurable (Function.uncurry g) :=
    slabSourceExtension_stronglyMeasurable hfm
  have hgeq (s : ℝ) (hs : s ∈ Icc 0 t) : g s = f s :=
    slabSourceExtension_of_mem hs f
  have hgs (s : ℝ) : ContDiff ℝ ∞ (g s) := by
    by_cases hs : s ∈ Icc 0 t
    · rw [hgeq s hs]
      exact hf s hs
    · have heq : g s = fun _ => (0 : F) := by
        funext y
        simp only [g, slabSourceExtension, if_neg hs]
      rw [heq]
      exact contDiff_const
  have hdgm := spatial_fderiv_stronglyMeasurable hgm
    (fun s => (hgs s).differentiable (by simp))
  obtain ⟨B0, hB0⟩ := hbound 0
  obtain ⟨B1, hB1⟩ := hbound 1
  obtain ⟨B2, hB2⟩ := hbound 2
  have hcommute := heatDuhamel_fderiv_commutes ht hgm hdgm
    (fun s _ => (hgs s).of_le (by simp))
    (C := B0) (D := B1)
    (fun s hs y => by
      rw [hgeq s hs]
      simpa only [norm_iteratedFDeriv_zero] using hB0 s hs y)
    (fun s hs y => by
      rw [hgeq s hs]
      simpa only [norm_iteratedFDeriv_one] using hB1 s hs y)
  rw [← heatDuhamel_slabSourceExtension ⟨ht, le_rfl⟩ f, hcommute]
  exact (heatDuhamel_c1_bound hC ht hdgm
    (fun s _ => (contDiff_infty_iff_fderiv.mp (hgs s)).2.of_le (by simp))
    (fun s hs => ⟨B2, fun y => by
      rw [hgeq s ⟨hs.1, hs.2.le⟩]
      simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
        using hB2 s ⟨hs.1, hs.2.le⟩ y⟩)
    (fun s hs y => by
      rw [hgeq s hs]
      exact hdf s hs y) x).2

end PoincareConjecture.M35.RadialGauge
