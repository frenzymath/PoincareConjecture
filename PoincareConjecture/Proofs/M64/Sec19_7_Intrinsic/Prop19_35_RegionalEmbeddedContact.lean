import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalFirstContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalRayInjectivity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_embedded_regional_contact_times
    (N : IntrinsicAnnulus) {K : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi)
    {a b : ℝ} (hinj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    {C U V : Set AnnulusCoordinates} (hC : IsCompact C)
    (havoid : ∀ p ∈ Ioo a b, intrinsicAnnulusBoundary 1 p ∉ C)
    (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ C)
    (hfV : frontier V = frontier U) (hsub : closure U ⊆ standardAnnulusDomain)
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates)
    (hbase : ∀ p ∈ Ioo a b, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p ∈ Ioo a b, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hinward : ∀ p ∈ Ioo a b, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hunit : ∀ p ∈ Ioo a b,
      N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    {R : ℝ} (hR : 0 < R) (annularHeight : ℝ → ℝ)
    (hAnn : ∀ p ∈ Ioo a b, 0 < annularHeight p ∧
      (annularHeight p = R ∨ ‖e !₂[p, annularHeight p]‖ = 1 ∨
        ‖e !₂[p, annularHeight p]‖ = 2))
    (hgeo : ∀ p ∈ Ioo a b, N.metric.IsGeodesicOn
      (fun t => e !₂[p, t]) (Icc 0 (annularHeight p))) :
    ∃ height : ℝ → ℝ, Measurable height ∧
      (∀ p ∉ Ioo a b, height p = 0) ∧
      (∀ p ∈ Ioo a b, 0 < height p ∧ height p ≤ R ∧ height p ≤ annularHeight p ∧
        (∀ t ∈ Ioo (0 : ℝ) (height p), e !₂[p, t] ∈ U) ∧
        e !₂[p, height p] ∈ closure U ∧
        (height p = R ∨ e !₂[p, height p] ∈ frontier U)) ∧
      ∀ p ∈ Ioo a b, InjOn (fun t => e !₂[p, t]) (Icc 0 (height p)) := by
  obtain ⟨height, hh, hzero, hcontact⟩ :=
    m64Intrinsic_exists_measurable_regional_contact_times hinj hC havoid
      hU hV hdisj hfU hfV hsub e he.continuous normal hbase hderiv hinward
      hR annularHeight hAnn
  refine ⟨height, hh, hzero, hcontact, ?_⟩
  intro p hp
  let q : ℝ → AnnulusCoordinates := fun t => e !₂[p, t]
  have hq : ContDiff ℝ ∞ q := he.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun _ : ℝ => p)
      exact contDiff_const
    · change ContDiff ℝ ∞ (fun t : ℝ => t)
      exact contDiff_id)
  have hq0 : q 0 = intrinsicAnnulusBoundary 1 p := hbase p hp
  have hqd0 : deriv q 0 = normal p := (hderiv p hp).deriv
  have hqnorm : ‖q 0‖ = 1 := by
    rw [hq0]
    exact m64Intrinsic_inner_boundary_norm p
  have hqinward : 0 < inner ℝ (q 0) (deriv q 0) := by
    rw [hq0, hqd0]
    exact hinward p hp
  have hqUnit0 : N.metric.inner (q 0) (curveVelocity (n := 2) q 0)
      (curveVelocity (n := 2) q 0) = 1 := by
    rw [m64Intrinsic_curveVelocity_eq_deriv, hqd0]
    erw [hq0]
    exact hunit p hp
  have hIcc : Icc (0 : ℝ) (height p) ⊆ Icc 0 (annularHeight p) :=
    Icc_subset_Icc le_rfl (hcontact p hp).2.2.1
  have hspeed := m64Intrinsic_geodesic_velocity_unit N
    (hcontact p hp).1 (hgeo p hp) hIcc hqUnit0
  apply m64Intrinsic_regional_ray_injOn N hK hsmall hU hV hpV hbV
    hdisj hcover hfV.symm hsub hq (fun t ht => hgeo p hp t (hIcc ht))
    (hcontact p hp).1 hqnorm hqinward
  · intro t ht
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hspeed t ht
  · exact (hcontact p hp).2.2.2.1

end PoincareConjecture
