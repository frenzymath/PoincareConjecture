import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelHessianDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable local instance m35DuhamelThirdJetsLocal1 :
    NormedAddCommGroup (V →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35DuhamelThirdJetsLocal2 :
    NormedSpace ℝ (V →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

theorem heatDuhamel_fderiv_eq_of_slab
    {f : ℝ → V → F} {t : ℝ} (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (fun p : Icc 0 t × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B) :
    fderiv ℝ (heatDuhamel f t) = heatDuhamel (fun s => fderiv ℝ (f s)) t := by
  rw [heatDuhamel_fderiv_slab_eq ht hfm hf hbound,
    heatDuhamel_slabSourceExtension ⟨ht, le_rfl⟩]

private theorem slab_derivative_bounds {f : ℝ → V → F} {t : ℝ}
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B) :
    ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (f s)) x‖ ≤ B := by
  intro j
  obtain ⟨B, hB⟩ := hbound (j + 1)
  exact ⟨B, fun s hs x => by rw [norm_iteratedFDeriv_fderiv]; exact hB s hs x⟩

theorem heatDuhamel_weighted_third_derivative_bound
    {f : ℝ → V → F} {t C : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hfm : StronglyMeasurable (fun p : Icc 0 t × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B)
    (hddf : ∀ s ∈ Icc 0 t, ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (f s)) x‖ ≤ C) (x : V) :
    (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (heatDuhamel f t))) x‖ ≤
      C * heatC1Gain (n + 1) t := by
  rw [heatDuhamel_fderiv_eq_of_slab ht hfm hf hbound]
  exact heatDuhamel_weighted_hessian_bound ht hC
    (spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 t => f s.1) hfm
      (fun s => (hf s.1 s.2).differentiable (by simp)))
    (fun s hs => (contDiff_infty_iff_fderiv.mp (hf s hs)).2)
    (slab_derivative_bounds hbound) hddf x

theorem heatDuhamel_weighted_third_derivative_difference_bound
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
    (hdf : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (f s)) x‖ ≤ C)
    (hdg : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (g s)) x‖ ≤ D)
    (hdfg : ∀ s ∈ Icc 0 t, ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (f s)) x - fderiv ℝ (fderiv ℝ (g s)) x‖ ≤ H)
    (x : V) :
    (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (heatDuhamel f t))) x -
      fderiv ℝ (fderiv ℝ (fderiv ℝ (heatDuhamel g t))) x‖ ≤
        H * heatC1Gain (n + 1) t := by
  rw [heatDuhamel_fderiv_eq_of_slab ht hfm hf hfb,
    heatDuhamel_fderiv_eq_of_slab ht hgm hg hgb]
  exact heatDuhamel_weighted_hessian_difference_bound ht hC hD hH
    (spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 t => f s.1) hfm
      (fun s => (hf s.1 s.2).differentiable (by simp)))
    (spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 t => g s.1) hgm
      (fun s => (hg s.1 s.2).differentiable (by simp)))
    (fun s hs => (contDiff_infty_iff_fderiv.mp (hf s hs)).2)
    (fun s hs => (contDiff_infty_iff_fderiv.mp (hg s hs)).2)
    (slab_derivative_bounds hfb) (slab_derivative_bounds hgb) hdf hdg hdfg x

end PoincareConjecture.M35.RadialGauge
