import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalDensity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MeasurableContact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_uniform_measurable_normal_strip
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ N : IntrinsicAnnulus, N.GaussianCurvatureBound K →
        ∃ (u : ℝ × ℝ → AnnulusCoordinates) (height : ℝ → ℝ),
          ContDiff ℝ ∞ u ∧ Measurable height ∧
          (∀ s, u (s, 0) = intrinsicAnnulusBoundary 1 s) ∧
          (∀ s, 0 < height s ∧ height s ≤ R ∧
            (∀ t ∈ Ioo (0 : ℝ) (height s), 1 < ‖u (s, t)‖ ∧ ‖u (s, t)‖ < 2) ∧
            u (s, height s) ∈ standardAnnulusDomain ∧
            (height s = R ∨ ‖u (s, height s)‖ = 1 ∨ ‖u (s, height s)‖ = 2)) ∧
          ∀ a : ℝ, intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
            ∃ S I : Set ℝ, IsOpen S ∧ IsOpen I ∧ a ∈ S ∧ Icc (0 : ℝ) (height a) ⊆ I ∧
              (∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I) ∧
              ∀ t ∈ Icc (0 : ℝ) (height a),
                (∀ v : ℝ × ℝ,
                  (1 - delta) ^ 2 *
                    ((intrinsicBoundarySpeed N.metric 1 a) ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
                    N.metric.inner (u (a, t))
                      (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) ∧
                Function.Injective (fderiv ℝ u (a, t)) ∧
                (1 - delta) ^ 2 * intrinsicBoundarySpeed N.metric 1 a ≤
                  N.metric.pullbackVolumeDensity
                    (fun z : AnnulusCoordinates => u (z 0, z 1)) !₂[a, t] := by
  obtain ⟨R, hR, hRsmall, hstrip⟩ :=
    m64Intrinsic_exists_uniform_normal_strip K hdelta hdelta1 halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro N hK
  obtain ⟨normal, u, _, hu, hn, hinit, hvelocity, hpoint⟩ := hstrip N hK
  obtain ⟨height, hheight, hcontact⟩ := m64Intrinsic_exists_measurable_contact_times
    hu.continuous hR (fun a => m64Intrinsic_inward_curve_enters_annulus
      (hinit a) (hvelocity a) (hn a).2.2)
  refine ⟨u, height, hu, hheight, hinit, hcontact, ?_⟩
  intro a ha
  obtain ⟨b, S, I, hb, hbR, hS, hI, haS, hsub, hgeo,
    hinside, _, hend, hmetric⟩ := hpoint a ha
  have heq : b = height a := m64Intrinsic_first_annulus_contact_unique
    hb (hcontact a).1 hbR (hcontact a).2.1 hinside (hcontact a).2.2.1
      hend (hcontact a).2.2.2.2
  subst b
  refine ⟨S, I, hS, hI, haS, hsub, hgeo, ?_⟩
  intro t ht
  exact ⟨(hmetric t ht).1, (hmetric t ht).2,
    m64Intrinsic_normal_map_density_lower N.metric
      (hu.differentiable (by simp) (a, t)) (hmetric t ht).1⟩

end PoincareConjecture
