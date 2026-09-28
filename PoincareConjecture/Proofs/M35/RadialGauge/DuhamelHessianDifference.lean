import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

private theorem slab_extension_contDiff {f : ℝ → V → F} {t : ℝ}
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s)) (s : ℝ) :
    ContDiff ℝ ∞ (slabSourceExtension t f s) := by
  by_cases hs : s ∈ Icc 0 t
  · rw [slabSourceExtension_of_mem hs]
    exact hf s hs
  · have heq : slabSourceExtension t f s = fun _ => (0 : F) := by
      funext x
      simp only [slabSourceExtension, if_neg hs]
    rw [heq]
    exact contDiff_const

private theorem slab_fderiv_measurable {f : ℝ → V → F} {t : ℝ}
    (hfm : StronglyMeasurable (fun p : Icc 0 t × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s)) :
    StronglyMeasurable
      (Function.uncurry (slabSourceExtension t (fun s => fderiv ℝ (f s)))) := by
  apply slabSourceExtension_stronglyMeasurable
  exact spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 t => f s.1) hfm
    (fun s => (hf s.1 s.2).differentiable (by simp))



theorem heatDuhamel_fderiv_slab_eq
    {f : ℝ → V → F} {t : ℝ} (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (fun p : Icc 0 t × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B) :
    fderiv ℝ (heatDuhamel f t) =
      heatDuhamel (slabSourceExtension t (fun s => fderiv ℝ (f s))) t := by
  let g := slabSourceExtension t f
  have hgm : StronglyMeasurable (Function.uncurry g) :=
    slabSourceExtension_stronglyMeasurable hfm
  have hgs := slab_extension_contDiff hf
  have hdgm := spatial_fderiv_stronglyMeasurable hgm
    (fun s => (hgs s).differentiable (by simp))
  obtain ⟨B0, hB0⟩ := hbound 0
  obtain ⟨B1, hB1⟩ := hbound 1
  have heq := heatDuhamel_fderiv_commutes ht hgm hdgm
    (fun s _ => (hgs s).of_le (by simp)) (C := B0) (D := B1)
    (fun s hs x => by
      rw [show g s = f s from slabSourceExtension_of_mem hs f]
      simpa only [norm_iteratedFDeriv_zero] using hB0 s hs x)
    (fun s hs x => by
      rw [show g s = f s from slabSourceExtension_of_mem hs f]
      simpa only [norm_iteratedFDeriv_one] using hB1 s hs x)
  rw [← heatDuhamel_slabSourceExtension ⟨ht, le_rfl⟩ f, heq]
  rw [show (fun s => fderiv ℝ (g s)) =
    slabSourceExtension t (fun s => fderiv ℝ (f s)) from fderiv_slabSourceExtension t f]



theorem heatDuhamel_weighted_hessian_difference_bound
    {f g : ℝ → V → F} {t C D H : ℝ} (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hfm : StronglyMeasurable (fun p : Icc 0 t × V => f p.1.1 p.2))
    (hgm : StronglyMeasurable (fun p : Icc 0 t × V => g p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s))
    (hg : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (g s))
    (hfb : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B)
    (hgb : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (g s) x‖ ≤ B)
    (hdf : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (f s) x‖ ≤ C)
    (hdg : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (g s) x‖ ≤ D)
    (hdfg : ∀ s ∈ Icc 0 t, ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (f s) x - fderiv ℝ (g s) x‖ ≤ H) (x : V) :
    (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (heatDuhamel f t)) x -
      fderiv ℝ (fderiv ℝ (heatDuhamel g t)) x‖ ≤ H * heatC1Gain (n + 1) t := by
  rw [heatDuhamel_fderiv_slab_eq ht hfm hf hfb, heatDuhamel_fderiv_slab_eq ht hgm hg hgb]
  let df := slabSourceExtension t (fun s => fderiv ℝ (f s))
  let dg := slabSourceExtension t (fun s => fderiv ℝ (g s))
  have hdf_eq (s : ℝ) (hs : s ∈ Icc 0 t) : df s = fderiv ℝ (f s) :=
    slabSourceExtension_of_mem hs _
  have hdg_eq (s : ℝ) (hs : s ∈ Icc 0 t) : dg s = fderiv ℝ (g s) :=
    slabSourceExtension_of_mem hs _
  obtain ⟨Bf, hBf⟩ := hfb 2
  obtain ⟨Bg, hBg⟩ := hgb 2
  exact (heatDuhamel_c1_difference_bound hC hD hH ht
    (slab_fderiv_measurable hfm hf) (slab_fderiv_measurable hgm hg)
    (fun s hs => by
      change ContDiff ℝ 1 (df s)
      rw [hdf_eq s hs]
      exact (contDiff_infty_iff_fderiv.mp (hf s hs)).2.of_le (by simp))
    (fun s hs => by
      change ContDiff ℝ 1 (dg s)
      rw [hdg_eq s hs]
      exact (contDiff_infty_iff_fderiv.mp (hg s hs)).2.of_le (by simp))
    (fun s hs => ⟨Bf, fun y => by
      change ‖fderiv ℝ (df s) y‖ ≤ Bf
      rw [hdf_eq s ⟨hs.1, hs.2.le⟩]
      simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
        using hBf s ⟨hs.1, hs.2.le⟩ y⟩)
    (fun s hs => ⟨Bg, fun y => by
      change ‖fderiv ℝ (dg s) y‖ ≤ Bg
      rw [hdg_eq s ⟨hs.1, hs.2.le⟩]
      simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
        using hBg s ⟨hs.1, hs.2.le⟩ y⟩)
    (fun s hs y => by
      change (1 + ‖y‖) * ‖df s y‖ ≤ C
      rw [hdf_eq s hs]
      exact hdf s hs y)
    (fun s hs y => by
      change (1 + ‖y‖) * ‖dg s y‖ ≤ D
      rw [hdg_eq s hs]
      exact hdg s hs y)
    (fun s hs y => by
      change (1 + ‖y‖) * ‖df s y - dg s y‖ ≤ H
      rw [hdf_eq s hs, hdg_eq s hs]
      exact hdfg s hs y) x).2

end PoincareConjecture.M35.RadialGauge
