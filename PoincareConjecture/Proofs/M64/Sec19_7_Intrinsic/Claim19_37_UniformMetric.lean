import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalExpansion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_uniform_normal_metric_radius
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ b : ℝ, 0 < b → b ≤ R → ∀ (N : IntrinsicAnnulus) (radius : ℝ), radius ≠ 0 →
        N.GaussianCurvatureBound K →
        ∀ (u : ℝ × ℝ → AnnulusCoordinates) (S I : Set ℝ),
          IsOpen S → IsOpen I → Icc (0 : ℝ) b ⊆ I →
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I) →
          (∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I) →
          (∀ s ∈ S, u (s, 0) = intrinsicAnnulusBoundary radius s) →
          ∀ normal : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ normal →
            (∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s)
              (normal s) (normal s) = 1) →
            (∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s) (normal s)
              (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) s) = 0) →
            (∀ s ∈ S, curveVelocity (n := 2) (fun t => u (s, t)) 0 = normal s) →
            ∀ a ∈ S,
              intrinsicGeodesicCurvature N.metric N.connection radius a ≤ alpha →
              (∀ t ∈ Ioo (0 : ℝ) b, u (a, t) ∈ standardAnnulusDomain) →
              ∀ t ∈ Icc (0 : ℝ) b,
                (∀ v : ℝ × ℝ,
                  (1 - delta) ^ 2 *
                    ((intrinsicBoundarySpeed N.metric radius a) ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
                    N.metric.inner (u (a, t))
                      (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) ∧
                Function.Injective (fderiv ℝ u (a, t)) := by
  obtain ⟨R, hR, hRsmall, hexpansion⟩ :=
    m64Intrinsic_exists_uniform_normal_expansion_subinterval_radius K hdelta hdelta1 halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro b hb hbR N radius hradius hK u S I hS hI hsub hu hgeo hboundary
    normal hnormal hunit horth hvelocity a ha hturn hmap
  obtain ⟨W, hW⟩ := hexpansion b hb hbR N radius hradius hK u S I hS hI hsub hu
    hgeo hboundary normal hnormal hunit horth hvelocity a ha hturn hmap
  have hunit0 : N.metric.inner (u (a, 0))
      (curveVelocity (n := 2) (fun t => u (a, t)) 0)
      (curveVelocity (n := 2) (fun t => u (a, t)) 0) = 1 := by
    erw [hvelocity a ha, hboundary a ha]
    exact hunit a
  have hunitTime := m64Intrinsic_geodesic_velocity_unit N hb (hgeo a ha) hsub hunit0
  have horthTime := m64Intrinsic_normal_variation_orthogonal N hS hI hu hgeo hboundary
    hnormal hunit horth hvelocity ha hb hsub
  intro t ht
  have hdiff : DifferentiableAt ℝ u (a, t) := (hu.contDiffOn.contDiffAt
    ((hS.prod hI).mem_nhds ⟨ha, hsub ht⟩)).differentiableAt (by simp)
  exact m64Intrinsic_normal_variation_metric_lower N hdiff (sub_pos.mpr hdelta1)
    (by linarith) (m64Intrinsic_boundarySpeed_pos N hradius a)
    (hunitTime t ht) (horthTime t ht) (hW t ht).2.2.2.2

end PoincareConjecture
