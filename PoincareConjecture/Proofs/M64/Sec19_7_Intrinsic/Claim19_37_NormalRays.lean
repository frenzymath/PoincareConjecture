import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_FirstExit













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_exists_normal_rays_until_exit
    (N : IntrinsicAnnulus) {R : ℝ} (hR : 0 < R) :
    ∃ normal : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ normal ∧
      (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
      ∀ a : ℝ, ∃ b left right : ℝ,
        0 < b ∧ b ≤ R ∧ 0 < left ∧ 0 < right ∧
        ∃ gamma : ℝ → AnnulusCoordinates,
          N.metric.IsGeodesicOn gamma (Ioo (-left) (b + right)) ∧
          gamma 0 = intrinsicAnnulusBoundary 1 a ∧ HasDerivAt gamma (normal a) 0 ∧
          (∀ t ∈ Icc (0 : ℝ) b,
            N.metric.inner (gamma t) (curveVelocity (n := 2) gamma t)
              (curveVelocity (n := 2) gamma t) = 1) ∧
          (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2) ∧
          gamma b ∈ standardAnnulusDomain ∧
          (b = R ∨ ‖gamma b‖ = 1 ∨ ‖gamma b‖ = 2) := by
  obtain ⟨normal, hnormal, hn, hfamily⟩ :=
    m64Intrinsic_exists_local_normal_geodesic_variation N (by norm_num : (1 : ℝ) ≠ 0)
  refine ⟨normal, hnormal, hn, ?_⟩
  intro a
  obtain ⟨U, epsilon, phase, _, ha, hepsilon, _, hinit, hgeo, hflow⟩ := hfamily a
  let q : ℝ → AnnulusCoordinates := fun t => (phase (a, t)).1
  have hz : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hqzero : q 0 = intrinsicAnnulusBoundary 1 a := congrArg Prod.fst (hinit a ha)
  have hqderiv : HasDerivAt q (normal a) 0 := by
    have h := (hflow a ha 0 hz).1
    rw [show (phase (a, 0)).2 = normal a from congrArg Prod.snd (hinit a ha)] at h
    exact h
  obtain ⟨eta, heta, hinside⟩ :=
    m64Intrinsic_inward_curve_enters_annulus hqzero hqderiv (hn a).2.2
  obtain ⟨b, left, right, hb, hbR, hleft, hright, gamma,
      hgamma, hgerm, hgammaInside, hend, hexit⟩ :=
    m64Intrinsic_exists_geodesic_to_annulus_exit N hR hepsilon heta (hgeo a ha) hinside
  have hzero : gamma 0 = intrinsicAnnulusBoundary 1 a := hgerm.self_of_nhds.trans hqzero
  have hderiv : HasDerivAt gamma (normal a) 0 := hqderiv.congr_of_eventuallyEq hgerm
  have hunit0 : N.metric.inner (gamma 0) (curveVelocity (n := 2) gamma 0)
      (curveVelocity (n := 2) gamma 0) = 1 := by
    rw [m64Intrinsic_curveVelocity_eq_deriv, hderiv.deriv]
    erw [hzero]
    exact (hn a).1
  refine ⟨b, left, right, hb, hbR, hleft, hright, gamma, hgamma, hzero, hderiv,
    ?_, hgammaInside, hend, hexit⟩
  exact m64Intrinsic_geodesic_velocity_unit N hb hgamma
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) hunit0

end PoincareConjecture
