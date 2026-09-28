import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarSmoothDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.H3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology InnerProductSpace ENNReal

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} {D : LeviCivitaData g} {Ω : Set Plane}

private theorem localized_smooth_forcing_data
    (e : OpenPartialHomeomorph Plane Plane)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (χ : Plane → ℝ) (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUs : closure U ⊆ e.source) (hone : ∀ z ∈ U, χ (e z) = 1)
    (B : NirenbergEuclidean.SmoothEllipticBilinearForm 2 univ)
    (hBA : EqOn B.a (divergenceCoefficients g e) U)
    (hBρ : EqOn B.c (g.pullbackVolumeDensity e) U)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ U)
    (u : H1Zero D Ω) (f : Lp ℝ 2 g.volumeMeasure) (f0 : Plane → ℝ)
    (hf0 : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f0)
    (hfae : (f : Plane → ℝ) =ᵐ[g.volumeMeasure] f0)
    (hsol : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ = ⟪f, toL2 D Ω v⟫_ℝ)
    (hu2 : Euclidean.MemWkp 2 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
      (U ∩ {z : Plane | 0 < z 0})) :
    let w := fun z => ψ z * chartPullback e (fun y => χ y * toL2 D Ω u y) z
    let Half := {z : Plane | 0 < z 0}
    Weak.MemW01p 2 w Half ∧ Euclidean.MemWkp 2 2 w Half ∧
      ∃ F : Plane → ℝ, Weak.MemW1p 2 F Half ∧
        ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Half →
          (∫ z in Half, ∑ i, ∑ j, B.a z i j * Euclidean.chosenWeakPartial' 2 j w Half z *
            fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z in Half, F z * φ z := by
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let G := chartPullback e (fun y => χ y * f0 y)
  let Half : Set Plane := {z | 0 < z 0}
  have hH : IsOpen Half := BoundaryTangential.isOpen_halfSpace
  have hUH : IsOpen (U ∩ Half) := hU.inter hH
  have hUHc : IsCompact (closure (U ∩ Half)) :=
    hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  obtain ⟨hu0, p, hp, hw, _, _, heq⟩ := Boundary.weakSolution_localized_divergence
    e he hei χ hχ hc hs hflat hU hUc hUs hone u f hsol
  have hchosen (j : Fin 2) : Euclidean.chosenWeakPartial' 2 j F (U ∩ Half)
      =ᵐ[volume.restrict (U ∩ Half)] p j := by
    exact Weak.HasWeakPartialDeriv.ae_eq hUH
      (Euclidean.chosenWeakPartial'_isWeakPartial_of_mem hu2.memW1p j)
      ((hw j).restrict hUH inter_subset_right)
      ((Euclidean.chosenWeakPartial'_memLp_of_mem hu2.memW1p j).locallyIntegrable (by norm_num))
      (((hp j).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)).locallyIntegrable
        (by norm_num))
  have hGs : ContDiff ℝ ∞ G := contDiff_chartPullback e he (hχ.mul hf0)
    hc.mul_right (tsupport_mul_subset_left.trans hs)
  have hGc : HasCompactSupport G := hasCompactSupport_chartPullback e
    hc.mul_right (tsupport_mul_subset_left.trans hs)
  have hG : Euclidean.MemWkp 1 2 G (U ∩ Half) :=
    (Euclidean.MemWkp_of_smooth_compactSupport isOpen_univ hGs hGc (subset_univ _)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1).mono_set (by norm_num) hUH (subset_univ _)
  let source : Plane → ℝ := fun z => B.c z * G z
  have hsource : Euclidean.MemWkp 1 2 source (U ∩ Half) :=
    BoundaryLocalization.memWkp_mul_smooth_of_isCompact_closure 1 hUH hUHc hG B.smooth_c
  have hcoord := (ae_restrict_iff' hUc.measurableSet).mp
    (g.ae_comp_on_compact e he hei hUc hUs hfae)
  have hB : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U ∩ Half →
      (∫ z in U ∩ Half, ∑ i, ∑ j, B.a z i j *
        Euclidean.chosenWeakPartial' 2 j F (U ∩ Half) z *
          fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z in U ∩ Half, source z * φ z := by
    intro φ hφ hφc hφs
    calc
      _ = ∫ z in U ∩ Half, ∑ i, ∑ j, divergenceCoefficients g e z i j * p j z *
          fderiv ℝ φ z (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hUH.measurableSet, eventually_all.mpr hchosen]
          with z hz hpz
        simp only [hBA hz.1, hpz]
      _ = _ := heq φ hφ hφc hφs
      _ = ∫ z in U ∩ Half, source z * φ z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hUH.measurableSet, ae_restrict_of_ae hcoord]
          with z hz hzf
        simp only [source, hBρ hz.1, G,
          chartPullback_apply e _ (hUs (subset_closure hz.1)), hone z hz.1, one_mul,
          hzf (subset_closure hz.1)]
  have hloc := BoundaryLocalization.localize_weak_divergence 1 hH hU B.a B.smooth_a
    hu2 hsource hψ hψc hψs hB
  exact ⟨BoundaryTangential.memW01p_mul_smooth hH hu0 hψ hψc,
    BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset 2 hH hU hu2 hψ hψc hψs,
    _, hloc.1.memW1p, hloc.2⟩

theorem exists_local_memWkp_three_of_smooth_forcing (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain 2 Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph Plane Plane) (χ : Plane → ℝ) (V : Set Plane),
      (x : Plane) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ (u : H1Zero D Ω) (f : Lp ℝ 2 g.volumeMeasure) (f0 : Plane → ℝ),
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f0 → (f : Plane → ℝ) =ᵐ[g.volumeMeasure] f0 →
        (∀ v : H1Zero D Ω,
          ⟪u, v⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ = ⟪f, toL2 D Ω v⟫_ℝ) →
        Euclidean.MemWkp 3 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
          (V ∩ {z : Plane | 0 < z 0}) := by
  obtain ⟨e, χ, W, hx, hxW, hW, hWc, hWs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    Boundary.exists_local_memWkp_two_of_weakSolution D S x
  obtain ⟨U, hU, hxU, hUW, hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  have hUW' : U ⊆ W := subset_closure.trans hUW
  have hUs : closure U ⊆ e.source := hUW.trans (subset_closure.trans hWs)
  obtain ⟨B, hBA, hBρ⟩ := Boundary.exists_elliptic_form_on_compact (g := g) e he hei hUc hUs
  obtain ⟨T, hT, hxT, hTU, hTc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hU hxU
  obtain ⟨ψ, hψ, hψc, _, hψone, hψs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hTc hU hTU
  refine ⟨e, χ, T, hx, hxT (mem_singleton _), hT, hTc,
    hTU.trans (subset_closure.trans hUs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hUW' (hTU (subset_closure hz))), hflat, ?_⟩
  intro u f f0 hf0 hfae hsol
  have hH : IsOpen {z : Plane | 0 < z 0} := BoundaryTangential.isOpen_halfSpace
  have hu2 := (hreg u f hsol).mono_set (by norm_num) (hU.inter hH)
    (inter_subset_inter_left _ hUW')
  obtain ⟨hu0, hu2global, F, hF, heq⟩ := localized_smooth_forcing_data
    e he hei χ hχ hc hs hflat hU hUc hUs (fun z hz => hone z (hUW' hz))
    B (hBA.mono subset_closure) (hBρ.mono subset_closure) hψ hψc hψs
    u f f0 hf0 hfae hsol hu2
  have hu3 := BoundaryTangential.memWkp_three_of_weakEquation B hT hTc hu0 hu2global hF heq
  apply (Euclidean.MemWkp_congr_ae (by norm_num) (hT.inter hH) _).mp hu3
  filter_upwards [ae_restrict_mem (hT.inter hH).measurableSet] with z hz
  simp only [hψone z (subset_closure hz.1), one_mul]

theorem exists_annular_boundary_H3_correction (D : LeviCivitaData g) :
    ∃ u : H1Zero D scalarAnnulus,
      (∀ v : H1Zero D scalarAnnulus,
        gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
          annularBoundaryExtension annularBoundaryExtension_smooth
          annularBoundaryExtension_compact v) ∧
      ∀ x : closure scalarAnnulus,
        ∃ (e : OpenPartialHomeomorph Plane Plane) (χ : Plane → ℝ) (V : Set Plane),
          (x : Plane) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
          IsCompact (closure V) ∧ closure V ⊆ e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
          (∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0) ∧
          Euclidean.MemWkp 3 2 (chartPullback e
            (fun y => χ y * toL2 D scalarAnnulus u y)) (V ∩ {z : Plane | 0 < z 0}) := by
  obtain ⟨u, hu, -⟩ := exists_annular_harmonic_potential D
  let ell := boundaryForcing D scalarAnnulus annularBoundaryExtension
    annularBoundaryExtension_smooth annularBoundaryExtension_compact
  have hforce (v : H1Zero D scalarAnnulus) : gradientEnergy D scalarAnnulus u v = ell v := by
    induction v using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq ((gradientEnergy D scalarAnnulus) u).continuous ell.continuous
    | ih φ =>
      change gradientEnergy D scalarAnnulus u φ = boundaryForcing D scalarAnnulus
        annularBoundaryExtension annularBoundaryExtension_smooth
        annularBoundaryExtension_compact φ
      rw [boundaryForcing_eq_neg_gradient]
      exact eq_neg_of_add_eq_zero_left (hu φ)
  refine ⟨u, hforce, ?_⟩
  intro x
  let S := Classical.choice nonempty_scalarAnnulus_smoothDomain
  obtain ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    exists_local_memWkp_three_of_smooth_forcing D S x
  refine ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, ?_⟩
  apply hreg u (boundaryLaplacianL2 D annularBoundaryExtension
      annularBoundaryExtension_smooth annularBoundaryExtension_compact)
    (D.laplacian annularBoundaryExtension)
    (D.contMDiff_laplacian annularBoundaryExtension_smooth)
  · exact ((D.continuous_laplacian annularBoundaryExtension_smooth).memLp_of_hasCompactSupport
      (D.hasCompactSupport_laplacian annularBoundaryExtension_compact)).coeFn_toLp
  · exact hforce

end PoincareConjecture.M64Uniformization
