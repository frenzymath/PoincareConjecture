import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarRadialBarriers













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem annular_harmonic_affine_comparison {H φ : Plane → ℝ}
    (hHc : Continuous H) (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hφs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ)
    (hφlap : ∀ x ∈ scalarAnnulus, 0 ≤ D.laplacian φ x) (a C : ℝ)
    (hboundary : ∀ x, scalarAnnulusDefining x = 0 → φ x - a * H x ≤ C) :
    ∀ x, 0 ≤ scalarAnnulusDefining x → φ x - a * H x ≤ C := by
  apply annular_subharmonic_le_boundary D
    (hφs.continuous.sub (continuous_const.mul hHc))
    (hφs.contMDiffOn.sub (contMDiffOn_const.mul hHs)) ?_ hboundary
  intro x hx
  obtain ⟨U, hUs, -, -, hUH⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hHs hx
  have heq : (fun y => φ y - a * U y) =ᶠ[𝓝 x] (fun y => φ y - a * H y) := by
    filter_upwards [hUH] with y hy
    rw [hy]
  have haU : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => a * U y) :=
    contMDiff_const.mul hUs
  have h := D.laplacian_sub hφs haU x
  rw [D.laplacian_eq_of_eventuallyEq heq, D.laplacian_const_mul,
    D.laplacian_eq_of_eventuallyEq hUH, hlap x hx, mul_zero, sub_zero] at h
  change 0 ≤ D.laplacian (fun y => φ y - a * H y) x
  rw [h]
  exact hφlap x hx







theorem annular_harmonic_strict_range {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨alpha, halpha, hbarrier⟩ := exists_annular_radial_exponential_barriers D
  have hs (c : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun y : Plane => Real.exp (c * ‖y‖ ^ 2)) := by
    apply contMDiff_iff_contDiff.mpr
    exact Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.norm_sq ℝ))
  have hclosed (x : Plane) (hx : x ∈ scalarAnnulus) : 0 ≤ scalarAnnulusDefining x :=
    ((scalarAnnulusDefining_pos x).mpr hx).le
  have hu := annular_harmonic_affine_comparison D hHc hHs hlap (hs alpha)
    (fun x hx => (hbarrier x (hclosed x hx)).1.le)
    (Real.exp (alpha * 4) - Real.exp alpha) (Real.exp alpha) (fun x hx => by
      rcases (scalarAnnulusDefining_zero x).mp hx with h | h
      · simp [h, hinner x h]
      · norm_num [h, houter x h])
  have hl := annular_harmonic_affine_comparison D hHc hHs hlap (hs (-alpha))
    (fun x hx => (hbarrier x (hclosed x hx)).2.le)
    (-(Real.exp (-alpha) - Real.exp (-alpha * 4))) (Real.exp (-alpha)) (fun x hx => by
      rcases (scalarAnnulusDefining_zero x).mp hx with h | h
      · simp [h, hinner x h]
      · norm_num [h, houter x h])
  have hap : 0 < Real.exp (alpha * 4) - Real.exp alpha := by
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have han : 0 < Real.exp (-alpha) - Real.exp (-alpha * 4) := by
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  intro x hx
  have hnormpos : 0 < ‖x‖ := lt_trans zero_lt_one hx.1
  have hsqlo : 1 < ‖x‖ ^ 2 := by nlinarith [hx.1]
  have hsqhi : ‖x‖ ^ 2 < 4 := by nlinarith [hx.2]
  have hup := hu x (hclosed x hx)
  have hlo := hl x (hclosed x hx)
  have hexpup : Real.exp alpha < Real.exp (alpha * ‖x‖ ^ 2) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  have hexplo : Real.exp (-alpha * 4) < Real.exp (-alpha * ‖x‖ ^ 2) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  constructor
  · nlinarith
  · nlinarith







theorem exists_strict_annular_harmonic_potential :
    ∃ (H : Plane → ℝ) (u : H1Zero D scalarAnnulus),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact u : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      (∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) ∧
      ∀ v : H1Zero D scalarAnnulus,
        gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
          annularBoundaryExtension annularBoundaryExtension_smooth
          annularBoundaryExtension_compact v := by
  obtain ⟨H, u, hHc, hHs, hHae, hlap, hinner, houter, hforce⟩ :=
    exists_annular_continuous_harmonic_potential D
  exact ⟨H, u, hHc, hHs, hHae, hlap, hinner, houter,
    annular_harmonic_strict_range D hHc hHs hlap hinner houter, hforce⟩

end PoincareConjecture.M64Uniformization
