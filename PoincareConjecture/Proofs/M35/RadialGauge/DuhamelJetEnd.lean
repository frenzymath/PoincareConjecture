import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelEnd
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelThirdJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable local instance m35DuhamelJetEndLocal1 :
    NormedAddCommGroup (V →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35DuhamelJetEndLocal2 :
    NormedSpace ℝ (V →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

theorem heatDuhamel_derivatives_weighted_vanish_uniformly
    {f : ℝ → V → F} {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hfm : StronglyMeasurable (fun p : Icc 0 T × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B)
    (hdf : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (f s) x‖ ≤ C)
    (hend : ∀ e > 0, ∃ R : ℝ, ∀ s ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (f s) x‖ < e) :
    ∀ e > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (heatDuhamel f t) x‖ < e ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x‖ < e := by
  let df := fun s => fderiv ℝ (f s)
  have hdfs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (df s) :=
    fun s hs => (contDiff_infty_iff_fderiv.mp (hf s hs)).2
  have hdfm : StronglyMeasurable (fun p : Icc 0 T × V => df p.1.1 p.2) :=
    spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 T => f s.1) hfm
      (fun s => (hf s.1 s.2).differentiable (by simp))
  have hfirst (t : ℝ) (ht : t ∈ Icc 0 T) :
      fderiv ℝ (heatDuhamel f t) = heatDuhamel df t := by
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    exact heatDuhamel_fderiv_eq_of_slab ht.1
      (hfm.comp_measurable (g := fun p : Icc 0 t × V =>
        ((⟨p.1.1, hsub p.1.2⟩ : Icc 0 T), p.2)) (by fun_prop))
      (fun s hs => hf s (hsub hs))
      (fun j => by
        obtain ⟨B, hB⟩ := hbound j
        exact ⟨B, fun s hs => hB s (hsub hs)⟩)
  have hsecond (t : ℝ) (ht : t ∈ Icc 0 T) :
      fderiv ℝ (fderiv ℝ (heatDuhamel f t)) = heatDuhamelGradient df t := by
    rw [hfirst t ht]
    rw [← heatDuhamel_slabSourceExtension ht df,
      ← heatDuhamelGradient_slabSourceExtension ht df]
    funext x
    obtain ⟨B2, hB2⟩ := hbound 2
    exact heatDuhamel_fderiv_eq hC ht.1 (slabSourceExtension_stronglyMeasurable hdfm)
      (fun s hs => by
        rw [slabSourceExtension_of_mem ⟨hs.1, hs.2.trans ht.2⟩]
        exact (hdfs s ⟨hs.1, hs.2.trans ht.2⟩).of_le (by simp))
      (fun s hs => ⟨B2, fun y => by
        rw [slabSourceExtension_of_mem ⟨hs.1, hs.2.le.trans ht.2⟩]
        simpa only [df, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
          using hB2 s ⟨hs.1, hs.2.le.trans ht.2⟩ y⟩)
      (fun s hs y => by
        rw [slabSourceExtension_of_mem ⟨hs.1, hs.2.trans ht.2⟩]
        exact hdf s ⟨hs.1, hs.2.trans ht.2⟩ y) x
  intro e he
  obtain ⟨R1, hR1⟩ := heatDuhamel_weighted_vanishes_uniformly hT
    (fun s hs => (hdfs s hs).continuous) hdf hend e he
  obtain ⟨R2, hR2⟩ := heatDuhamelGradient_weighted_vanishes_uniformly
    (fun s hs => (hdfs s hs).continuous) hdf hend e he
  refine ⟨max R1 R2, fun t ht x hx => ?_⟩
  rw [hsecond t ht, hfirst t ht]
  exact ⟨hR1 t ht x ((le_max_left _ _).trans hx), hR2 t ht x ((le_max_right _ _).trans hx)⟩

end PoincareConjecture.M35.RadialGauge
