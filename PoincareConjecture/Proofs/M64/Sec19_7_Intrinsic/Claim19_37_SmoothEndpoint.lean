import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_ExtensionBalls
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open RiemannianMetric




theorem m64Intrinsic_exists_smooth_extended_normal_endpoint (N : IntrinsicAnnulus) :
    ∃ (G : RiemannianMetric 2 AnnulusCoordinates)
      (normal : ℝ → AnnulusCoordinates) (u : ℝ × ℝ → AnnulusCoordinates),
      (∀ p ∈ standardAnnulusDomain,
        G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients) ∧
      ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
      (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
      ∀ z : ℝ × ℝ, ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ gamma : ℝ → AnnulusCoordinates,
        G.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
        gamma 0 = intrinsicAnnulusBoundary 1 z.1 ∧
        HasDerivAt gamma (z.2 • normal z.1) 0 ∧ gamma 1 = u z := by
  classical
  obtain ⟨G, hG, hex⟩ := m64Intrinsic_exists_extension_with_geodesic_initial_data N
  obtain ⟨normal, hnormal, hn⟩ :=
    m64Intrinsic_exists_smooth_inward_boundary_normal N (by norm_num : (1 : ℝ) ≠ 0)
  choose epsilon hepsilon Gamma hGamma using fun z : ℝ × ℝ =>
    hex (intrinsicAnnulusBoundary 1 z.1) (z.2 • normal z.1)
  let u : ℝ × ℝ → AnnulusCoordinates := fun z => Gamma z 1
  have hu : ContDiff ℝ ∞ u := by
    apply contMDiff_iff_contDiff.mp
    intro z
    have hgeo : ∀ᶠ w in 𝓝 z, G.IsGeodesicOn (Gamma w) (Icc (0 : ℝ) 1) := by
      apply Eventually.of_forall
      intro w t ht
      exact (hGamma w).1 t ⟨by linarith [hepsilon w, ht.1],
        by linarith [hepsilon w, ht.2]⟩
    apply contMDiffAt_geodesic_endpoint hgeo (convex_Icc (0 : ℝ) 1)
      (a := 0) (b := 1) (by norm_num) (by norm_num)
    · have heq : (fun w => Gamma w 0) = fun w => intrinsicAnnulusBoundary 1 w.1 :=
        funext (fun w => (hGamma w).2.1)
      rw [heq]
      exact contMDiffAt_iff_contDiffAt.mpr
        ((m64Intrinsic_contDiff_boundary 1).contDiffAt.comp z contDiffAt_fst)
    · have heq : (fun w => deriv (fun t => extChartAt (𝓡 2) (Gamma z 0) (Gamma w t)) 0) =
          fun w => w.2 • normal w.1 := by
        funext w
        simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
          (hGamma w).2.2.deriv
      rw [heq]
      exact contDiffAt_snd.smul (hnormal.contDiffAt.comp z contDiffAt_fst)
  refine ⟨G, normal, u, hG, hnormal, hu, hn, ?_⟩
  intro z
  exact ⟨epsilon z, hepsilon z, Gamma z, (hGamma z).1,
    (hGamma z).2.1, (hGamma z).2.2, rfl⟩

end PoincareConjecture
