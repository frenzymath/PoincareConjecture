import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAnnulusBoundaryDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundarySeparation
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => Set.preimage (fun p : Plane => p 0) (Ioi (0 : ℝ))

private theorem chart_differential_ne_zero_of_linear_curve
    {H : Plane → ℝ} {x : Plane}
    (e : OpenPartialHomeomorph Plane Plane) (hx : x ∈ e.target)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0)
    {r : ℝ} (hr : 0 < r) {J : Plane →L[ℝ] ℝ}
    (hJ : HasFDerivWithinAt (H ∘ e) J
      (closure (Metric.ball (e.symm x) r ∩ Half)) (e.symm x))
    {b : ℝ → Plane} {v : Plane} (hb : HasDerivAt b v 0) (hb0 : b 0 = x)
    (hbmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), b t ∈ scalarAnnulus)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), c * t ≤ |H (b t) - H x|) : J ≠ 0 := by
  let p := e.symm ∘ b
  have heid := (contMDiffAt_iff_contDiffAt.mp
    (hei.contMDiffAt (e.open_target.mem_nhds hx))).differentiableAt (by simp)
  have hp : HasDerivAt p (fderiv ℝ e.symm x v) 0 :=
    heid.hasFDerivAt.comp_hasDerivAt_of_eq 0 hb hb0.symm
  have hp0 : p 0 = e.symm x := by simp only [p, Function.comp_apply, hb0]
  have hpball : ∀ᶠ t in 𝓝[>] (0 : ℝ), p t ∈ Metric.ball (e.symm x) r := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact hp.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds
      (by rw [hp0]; exact Metric.mem_ball_self hr))
  have hbt : ∀ᶠ t in 𝓝[>] (0 : ℝ), b t ∈ e.target := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact hb.continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds (by rwa [hb0]))
  let S := p ⁻¹' closure (Metric.ball (e.symm x) r ∩ Half)
  have hS : S ∈ 𝓝[>] (0 : ℝ) := by
    filter_upwards [hpball, hbt, hbmem] with t ht hte htA
    apply subset_closure
    refine ⟨ht, ?_⟩
    apply (hflat (p t) (e.map_target hte)).mp
    simpa only [p, Function.comp_apply, e.right_inv hte] using htA
  have hd : HasDerivWithinAt ((H ∘ e) ∘ p) (J (fderiv ℝ e.symm x v)) S 0 :=
    hJ.comp_hasDerivWithinAt_of_eq 0 hp.hasDerivWithinAt (fun _ ht => ht) hp0.symm
  have hd' : HasDerivWithinAt (H ∘ b) (J (fderiv ℝ e.symm x v)) (Ioi 0) 0 := by
    apply (hd.mono_of_mem_nhdsWithin hS).congr_of_eventuallyEq
    · filter_upwards [hbt] with t ht
      simp only [p, Function.comp_apply, e.right_inv ht]
    · simp only [p, Function.comp_apply, hb0, e.right_inv hx]
  have hlim := ((hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hd').norm
  have hle : c ≤ ‖J (fderiv ℝ e.symm x v)‖ := by
    apply ge_of_tendsto hlim
    filter_upwards [hbound, self_mem_nhdsWithin] with t ht htpos
    change 0 < t at htpos
    simp only [slope_def_field, Function.comp_apply, hb0, sub_zero,
      Real.norm_eq_abs, abs_div, abs_of_pos htpos]
    exact (le_div_iff₀ htpos).mpr ht
  intro hzero
  rw [hzero, zero_apply, norm_zero] at hle
  exact hc.not_ge hle

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem annular_boundary_differential_ne_zero
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {x : Plane} (hxnorm : ‖x‖ = 1 ∨ ‖x‖ = 2)
    (e : OpenPartialHomeomorph Plane Plane) (hx : x ∈ e.target)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0)
    {r : ℝ} (hr : 0 < r) {J : Plane →L[ℝ] ℝ}
    (hJ : HasFDerivWithinAt (H ∘ e) J
      (closure (Metric.ball (e.symm x) r ∩ Half)) (e.symm x)) : J ≠ 0 := by
  obtain ⟨c, hc, hsep⟩ :=
    annular_harmonic_linear_boundary_separation D hHc hHs hlap hinner houter
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 :=
    Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  rcases hxnorm with hnorm | hnorm
  · let b : ℝ → Plane := fun t => (1 + t) • x
    have hb : HasDerivAt b x 0 := by
      simpa only [b, id_eq, one_smul] using!
        ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x
    have hb0 : b 0 = x := by simp [b]
    have hbnorm {t : ℝ} (ht : 0 < t) : ‖b t‖ = 1 + t := by
      simp only [b, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + t), hnorm, mul_one]
    have hbmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), b t ∈ scalarAnnulus := by
      filter_upwards [hsmall] with t ht
      change 1 < ‖b t‖ ∧ ‖b t‖ < 2
      rw [hbnorm ht.1]
      constructor <;> linarith
    apply chart_differential_ne_zero_of_linear_curve e hx hei hflat hr hJ hb hb0 hbmem hc
    filter_upwards [hsmall, hbmem] with t ht htA
    have hs := (hsep (b t) ((scalarAnnulusDefining_pos _).mpr htA).le).1
    rw [hbnorm ht.1] at hs
    calc
      c * t ≤ H (b t) := by linarith
      _ ≤ |H (b t) - H x| := by rw [hinner x hnorm, sub_zero]; exact le_abs_self _
  · let b : ℝ → Plane := fun t => (1 - t / 2) • x
    have hb : HasDerivAt b ((-(1 / 2 : ℝ)) • x) 0 := by
      convert! ((hasDerivAt_const (0 : ℝ) 1).sub
        ((hasDerivAt_id (0 : ℝ)).div_const 2)).smul_const x using 1
      norm_num
    have hb0 : b 0 = x := by simp [b]
    have hbnorm {t : ℝ} (ht : t < 1) : ‖b t‖ = 2 - t := by
      rw [show b t = (1 - t / 2) • x from rfl, norm_smul,
        Real.norm_of_nonneg (by linarith : 0 ≤ 1 - t / 2), hnorm]
      ring
    have hbmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), b t ∈ scalarAnnulus := by
      filter_upwards [hsmall] with t ht
      change 1 < ‖b t‖ ∧ ‖b t‖ < 2
      rw [hbnorm ht.2]
      constructor <;> linarith
    apply chart_differential_ne_zero_of_linear_curve e hx hei hflat hr hJ hb hb0 hbmem hc
    filter_upwards [hsmall, hbmem] with t ht htA
    have hs := (hsep (b t) ((scalarAnnulusDefining_pos _).mpr htA).le).2
    rw [hbnorm ht.2] at hs
    calc
      c * t ≤ 1 - H (b t) := by linarith
      _ ≤ |H (b t) - H x| := by
        rw [houter x hnorm]
        have h := neg_le_abs (H (b t) - 1)
        linarith

theorem exists_annular_harmonic_potential_noncritical_boundary :
    ∃ H : Plane → ℝ,
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      ∀ x : closure scalarAnnulus, ‖(x : Plane)‖ = 1 ∨ ‖(x : Plane)‖ = 2 →
        ∃ (e : OpenPartialHomeomorph Plane Plane) (O : Set Plane)
          (J : Plane → Plane →L[ℝ] ℝ),
          (x : Plane) ∈ e.target ∧ e.symm x ∈ closure O ∧ IsOpen O ∧ Convex ℝ O ∧
          IsCompact (closure O) ∧ closure O ⊆ e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          (∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0) ∧
          (∃ r : ℝ, 0 < r ∧ O = Metric.ball (e.symm (x : Plane)) r ∩ Half) ∧
          ContinuousOn J e.source ∧ EqOn (fderiv ℝ (H ∘ e)) J O ∧
          (∀ z ∈ closure O, HasFDerivWithinAt (H ∘ e) (J z) (closure O) z) ∧
          J (e.symm x) ≠ 0 := by
  obtain ⟨H, hHc, hHs, hlap, hinner, houter, hboundary⟩ :=
    exists_annular_harmonic_potential_boundary_differential D
  refine ⟨H, hHc, hHs, hlap, hinner, houter, ?_⟩
  intro x hxn
  obtain ⟨e, O, J, hx, hxO, hO, hconv, hOc, hOs, he, hei, hflat, hshape,
    hJc, hJeq, hJderiv⟩ := hboundary x
  obtain ⟨r, hr, hshape'⟩ := hshape
  refine ⟨e, O, J, hx, hxO, hO, hconv, hOc, hOs, he, hei, hflat,
    ⟨r, hr, hshape'⟩, hJc, hJeq, hJderiv, ?_⟩
  apply annular_boundary_differential_ne_zero D hHc hHs hlap hinner houter
    hxn e hx hei hflat hr
  rw [← hshape']
  exact hJderiv (e.symm x) hxO

end PoincareConjecture.M64Uniformization
