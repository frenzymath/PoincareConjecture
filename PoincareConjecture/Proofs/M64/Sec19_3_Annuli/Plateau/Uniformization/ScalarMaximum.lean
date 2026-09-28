import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryValues
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationIsothermalMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Extrema

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem exists_annular_positive_laplacian_barrier :
    ∃ φ : Plane → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ ∧
      (∀ x, 0 < φ x) ∧ ∀ x, 0 ≤ scalarAnnulusDefining x → 0 < D.laplacian φ x := by
  let f : Plane → ℝ := fun x => x 0
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_iff_contDiff.mpr
      (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff
  let E : Plane → ℝ := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  have hEc : Continuous E := D.continuous_inner_gradient hf hf
  have hEp (x : Plane) : 0 < E x := by
    have h := M60.firstCoordinateGradient_zero_pos g D x
    rw [← M60.inner_firstCoordinateGradient g D x (M60.firstCoordinateGradient g D x)] at h
    exact h
  let K := {x : Plane | 0 ≤ scalarAnnulusDefining x}
  have hK : IsCompact K := scalarClosedAnnulus_isCompact
  have hKne : K.Nonempty := scalarClosedAnnulus_isConnected.nonempty
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne hEc.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hKne (D.continuous_laplacian hf).continuousOn
  let alpha := (|D.laplacian f b| + 1) / E a
  have halpha : 0 < alpha := div_pos (by positivity) (hEp a)
  have halphaE : alpha * E a = |D.laplacian f b| + 1 := div_mul_cancel₀ _ (hEp a).ne'
  let F : ℝ → ℝ := fun r => Real.exp (-alpha * r)
  have hF : ContDiff ℝ ∞ F := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hdF (r : ℝ) : deriv F r = -alpha * Real.exp (-alpha * r) := by
    have h := (Real.hasDerivAt_exp (-alpha * r)).comp r
      ((hasDerivAt_id r).const_mul (-alpha))
    simpa only [F, Function.comp_def, mul_one, one_mul, mul_comm] using h.deriv
  have hddF (r : ℝ) : deriv (deriv F) r = alpha ^ 2 * Real.exp (-alpha * r) := by
    rw [show deriv F = fun s => -alpha * F s from funext hdF]
    rw [deriv_const_mul _ (hF.differentiable (by simp) r), hdF]
    ring
  refine ⟨F ∘ f, contMDiff_iff_contDiff.mpr
    (hF.comp (contMDiff_iff_contDiff.mp hf)), fun _ => Real.exp_pos _, ?_⟩
  intro x hx
  have hmin' : E a ≤ E x := hmin hx
  have hmax' : D.laplacian f x ≤ D.laplacian f b := hmax hx
  have hpositive : 0 < alpha * E x - D.laplacian f x := by
    have hmul := mul_le_mul_of_nonneg_left hmin' halpha.le
    linarith [le_abs_self (D.laplacian f b)]
  rw [D.laplacian_comp hf hF, hdF, hddF]
  change 0 < -alpha * Real.exp (-alpha * f x) * D.laplacian f x +
    (alpha ^ 2 * Real.exp (-alpha * f x)) * E x
  have h := mul_pos (Real.exp_pos (-alpha * f x)) (mul_pos halpha hpositive)
  nlinarith

theorem annular_subharmonic_le_boundary {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, 0 ≤ D.laplacian H x) {C : ℝ}
    (hboundary : ∀ x, scalarAnnulusDefining x = 0 → H x ≤ C) :
    ∀ x, 0 ≤ scalarAnnulusDefining x → H x ≤ C := by
  obtain ⟨φ, hφ, hφpos, hφlap⟩ := exists_annular_positive_laplacian_barrier D
  let K := {x : Plane | 0 ≤ scalarAnnulusDefining x}
  have hK : IsCompact K := scalarClosedAnnulus_isCompact
  have hKne : K.Nonempty := scalarClosedAnnulus_isConnected.nonempty
  obtain ⟨p, hp, hφmax⟩ := hK.exists_isMaxOn hKne hφ.continuous.continuousOn
  intro x hx
  by_contra hfail
  have hCx : C < H x := lt_of_not_ge hfail
  let epsilon := (H x - C) / (2 * φ p)
  have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr hCx) (mul_pos (by norm_num) (hφpos p))
  have hepsilonM : epsilon * φ p = (H x - C) / 2 := by
    dsimp [epsilon]
    field_simp [(hφpos p).ne']
  let P : Plane → ℝ := fun y => H y + epsilon * φ y
  have hPc : Continuous P := hHc.add (continuous_const.mul hφ.continuous)
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hKne hPc.continuousOn
  have hyint : y ∈ interior K := by
    by_contra hyint
    have hyA : y ∉ scalarAnnulus := by
      simpa only [K, scalarClosedAnnulus_interior] using hyint
    have hyzero : scalarAnnulusDefining y = 0 := by
      have hynot : ¬ 0 < scalarAnnulusDefining y :=
        fun h => hyA ((scalarAnnulusDefining_pos y).mp h)
      exact le_antisymm (le_of_not_gt hynot) hy
    have hHbound := hboundary y hyzero
    have hφbound := mul_le_mul_of_nonneg_left (hφmax hy) hepsilon.le
    have hPx : P x ≤ P y := hmax hx
    have hxphi := mul_pos hepsilon (hφpos x)
    dsimp only [P] at hPx
    linarith
  have hyA : y ∈ scalarAnnulus := by
    simpa only [K, scalarClosedAnnulus_interior] using hyint
  obtain ⟨U, hUs, -, -, hUH⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hHs hyA
  have hlocal : IsLocalMax (fun z => U z + epsilon * φ z) y := by
    filter_upwards [isOpen_interior.mem_nhds hyint, hUH] with z hz hzU
    rw [hzU, hUH.self_of_nhds]
    exact hmax (interior_subset hz)
  have hnonpos := D.laplacian_nonpos_of_isLocalMax
    (hUs.add (contMDiff_const.mul hφ)) hlocal
  change D.laplacian (fun z => U z + epsilon * φ z) y ≤ 0 at hnonpos
  have hpert : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z => epsilon * φ z) :=
    contMDiff_const.mul hφ
  rw [D.laplacian_add hUs hpert, D.laplacian_const_mul,
    D.laplacian_eq_of_eventuallyEq hUH] at hnonpos
  have hpositive := mul_pos hepsilon (hφlap y hy)
  linarith [hlap y hyA]

theorem annular_harmonic_range {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∀ x, 0 ≤ scalarAnnulusDefining x → H x ∈ Icc (0 : ℝ) 1 := by
  have hu := annular_subharmonic_le_boundary D hHc hHs
    (fun x hx => (hlap x hx).ge) (C := 1) (fun x hx => by
      rcases (scalarAnnulusDefining_zero x).mp hx with h | h
      · rw [hinner x h]
        norm_num
      · rw [houter x h])
  have hn : ∀ x ∈ scalarAnnulus, 0 ≤ D.laplacian (fun y => -H y) x := by
    intro x hx
    have h := D.laplacian_const_mul (-1) H x
    simpa only [neg_one_mul, hlap x hx, neg_zero] using h.ge
  have hl := annular_subharmonic_le_boundary D hHc.neg hHs.neg hn
    (C := 0) (fun x hx => by
      change -H x ≤ 0
      rcases (scalarAnnulusDefining_zero x).mp hx with h | h
      · rw [hinner x h]
        norm_num
      · rw [houter x h]
        norm_num)
  intro x hx
  exact ⟨neg_nonpos.mp (hl x hx), hu x hx⟩

theorem exists_bounded_annular_harmonic_potential :
    ∃ (H : Plane → ℝ) (u : H1Zero D scalarAnnulus),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact u : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      (∀ x, 0 ≤ scalarAnnulusDefining x → H x ∈ Icc (0 : ℝ) 1) ∧
      ∀ v : H1Zero D scalarAnnulus,
        gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
          annularBoundaryExtension annularBoundaryExtension_smooth
          annularBoundaryExtension_compact v := by
  obtain ⟨H, u, hHc, hHs, hHae, hlap, hinner, houter, hforce⟩ :=
    exists_annular_continuous_harmonic_potential D
  exact ⟨H, u, hHc, hHs, hHae, hlap, hinner, houter,
    annular_harmonic_range D hHc hHs hlap hinner houter, hforce⟩

end PoincareConjecture.M64Uniformization
