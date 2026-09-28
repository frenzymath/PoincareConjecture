import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.H3








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

open Poincare.Analysis.Sobolev

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

local notation "E" => EuclideanSpace ℝ (Fin n)


theorem weakSolution_chosen_divergence
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {W : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWs : closure W ⊆ e.source) (hone : ∀ z ∈ W, χ (e z) = 1)
    (B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ)
    (hBA : EqOn B.a (divergenceCoefficients g e) W)
    (hBρ : EqOn B.c (g.pullbackVolumeDensity e) W)
    (u v : H1Zero D Ω)
    (hsol : ∀ w : H1Zero D Ω,
      ⟪u, w⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω w⟫_ℝ = ⟪toL2 D Ω v, toL2 D Ω w⟫_ℝ) :
    let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
    let G := chartPullback e (fun y => χ y * toL2 D Ω v y)
    let H := {z : E | 0 < z 0}
    Weak.MemW01p 2 F H ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ H →
        (∫ z in W ∩ H, ∑ i, ∑ j, B.a z i j *
          Euclidean.chosenWeakPartial' 2 j F (W ∩ H) z *
          fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z in W ∩ H, (B.c z * G z) * φ z := by
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  have hWH : IsOpen (W ∩ H) := hW.inter hH
  obtain ⟨hu0, p, hp, hw, _, _, heq⟩ := weakSolution_localized_divergence
    e he hei χ hχ hc hs hflat hW hWc hWs hone u (toL2 D Ω v) hsol
  have hu1 := Euclidean.MemW1p.mono_set hWH inter_subset_right hu0.1
  have hchosen (j : Fin n) : Euclidean.chosenWeakPartial' 2 j F (W ∩ H) =ᵐ[volume.restrict (W ∩ H)]
      p j := by
    exact Weak.HasWeakPartialDeriv.ae_eq hWH
      (Euclidean.chosenWeakPartial'_isWeakPartial_of_mem hu1 j)
      ((hw j).restrict hWH inter_subset_right)
      ((Euclidean.chosenWeakPartial'_memLp_of_mem hu1 j).locallyIntegrable (by norm_num))
      (((hp j).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)).locallyIntegrable
        (by norm_num))
  refine ⟨hu0, ?_⟩
  intro φ hφ hφc hφs
  calc
    _ = ∫ z in W ∩ H, ∑ i, ∑ j, divergenceCoefficients g e z i j * p j z *
        fderiv ℝ φ z (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hWH.measurableSet, eventually_all.mpr hchosen] with z hz hpz
      dsimp only [F, H] at hpz
      simp only [hBA hz.1, hpz]
    _ = _ := heq φ hφ hφc hφs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hWH.measurableSet] with z hz
      simp only [hBρ hz.1, chartPullback_apply e _ (hWs (subset_closure hz.1)),
        hone z hz.1, one_mul]

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
