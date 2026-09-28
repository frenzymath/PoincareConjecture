import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation
import Mathlib.Topology.UniformSpace.HeineCantor











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M28

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]




theorem eventually_exists_smooth_homeomorph_of_compact_displacement
    {D : ℝ × E → E} (hD : ContDiff ℝ ∞ D)
    {K : Set E} (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, tsupport (fun x => D (t, x)) ⊆ K)
    {t₀ : ℝ} (hzero : ∀ x : E, D (t₀, x) = 0) :
    ∀ᶠ t in 𝓝 t₀, ∃ e : E ≃ₜ E,
      (e : E → E) = (fun x => x + D (t, x)) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      ∀ x : E, x ∉ K → e x = x := by
  have hsection (t : ℝ) : ContDiff ℝ ∞ (fun x : E => D (t, x)) :=
    hD.comp (contDiff_const.prodMk contDiff_id)
  have hjoint : ContDiff ℝ ∞
      (fun p : (ℝ × E) × E => D (p.1.1, p.2)) :=
    hD.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hderiv : Continuous
      (fun p : ℝ × E => fderiv ℝ (fun x => D (p.1, x)) p.2) :=
    (hjoint.fderiv (n := ∞) contDiff_snd (by simp)).continuous
  have hderiv_zero (x : E) : fderiv ℝ (fun y => D (t₀, y)) x = 0 := by
    have hz : (fun y => D (t₀, y)) = (fun _ : E => (0 : E)) := funext hzero
    rw [hz, fderiv_const_apply]
  obtain ⟨V, hV, hclose⟩ := hK.mem_uniformity_of_prod
    (f := fun t x => fderiv ℝ (fun y => D (t, y)) x)
    (s := (univ : Set ℝ)) hderiv.continuousOn (mem_univ t₀)
    (Metric.dist_mem_uniformity (by norm_num : (0 : ℝ) < 1 / 2))
  have hV' : V ∈ 𝓝 t₀ := by simpa only [nhdsWithin_univ] using hV
  filter_upwards [hV'] with t ht
  have hsmall (x : E) : ‖fderiv ℝ (fun y => D (t, y)) x‖ ≤ (1 / 2 : ℝ) := by
    by_cases hx : x ∈ K
    · have hbound := hclose t ht x hx
      change dist (fderiv ℝ (fun y => D (t, y)) x)
        (fderiv ℝ (fun y => D (t₀, y)) x) < (1 / 2 : ℝ) at hbound
      rw [hderiv_zero, dist_zero_right] at hbound
      exact hbound.le
    · rw [fderiv_of_notMem_tsupport ℝ (f := fun y => D (t, y))
        (fun h => hx (hsupport t h)), norm_zero]
      norm_num
  have hf : ContDiff ℝ ∞ (fun x : E => x + D (t, x)) :=
    contDiff_id.add (hsection t)
  have hfclose (x : E) :
      ‖fderiv ℝ (fun y : E => y + D (t, y)) x - ContinuousLinearMap.id ℝ E‖ ≤
        (1 / 2 : ℝ≥0) := by
    have hd : fderiv ℝ (fun y : E => y + D (t, y)) x =
        ContinuousLinearMap.id ℝ E + fderiv ℝ (fun y => D (t, y)) x :=
      ((hasFDerivAt_id x).add
        (((hsection t).differentiable (by simp) x).hasFDerivAt)).fderiv
    rw [hd, add_sub_cancel_left]
    simpa using hsmall x
  obtain ⟨e, he, hes, hei⟩ :=
    Poincare.Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id
      hf (by norm_num : (1 / 2 : ℝ≥0) < 1) hfclose
  refine ⟨e, he, hes, hei, ?_⟩
  intro x hx
  have hz : D (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => D (t, y))
      (fun h => hx (hsupport t h))
  change (e : E → E) x = x
  rw [he]
  change x + D (t, x) = x
  rw [hz, add_zero]

end PoincareConjecture.M28
