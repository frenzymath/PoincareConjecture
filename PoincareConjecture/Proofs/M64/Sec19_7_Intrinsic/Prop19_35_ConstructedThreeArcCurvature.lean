import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_UnorientedThreeArcTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCurvatureLowerBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

theorem m64Intrinsic_constructed_three_arc_region_curvature_lower_bound
    (N : IntrinsicAnnulus)
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ t ∈ Ioo 0 (T false), deriv (gamma false) t ≠ 0)
    (hreg0 : deriv (gamma false) 0 ≠ 0)
    (horth : N.metric.inner (gamma false 0) (deriv (gamma false) 0) (deriv sigma 0) = 0)
    (hgeo : N.metric.IsGeodesicOn (gamma true) (Icc 0 (T true)))
    (hsgeo : N.metric.IsGeodesicOn sigma (Icc 0 S))
    (hunit : ∀ t ∈ Icc 0 (T true),
      N.metric.inner (gamma true t) (deriv (gamma true) t) (deriv (gamma true) t) = 1)
    (hsunit : ∀ t ∈ Icc 0 S, N.metric.inner (sigma t) (deriv sigma t) (deriv sigma t) = 1)
    (hind1 : LinearIndependent ℝ
      (![-deriv (gamma true) (T true), -deriv sigma S] : Fin 2 → AnnulusCoordinates))
    {a b : ℝ} (habound : a ≤ b)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    (hcircle : gamma false '' Icc 0 (T false) = intrinsicAnnulusBoundary 1 '' Icc a b)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward : 0 < inner ℝ (gamma false 0) (deriv sigma 0))
    (hsub : closure U ⊆ standardAnnulusDomain) :
    Real.pi / 2 - intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b ≤
      ∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure := by
  have hgreg (t : ℝ) (ht : t ∈ Ioo 0 (T true)) : deriv (gamma true) t ≠ 0 := by
    intro hz
    have hu := hunit t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hsreg (t : ℝ) (ht : t ∈ Icc 0 S) : deriv sigma t ≠ 0 := by
    intro hz
    have hu := hsunit t ht
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hregAll (e : Bool) : ∀ t ∈ Ioo 0 (T e), deriv (gamma e) t ≠ 0 := by
    cases e
    · exact hregular
    · exact hgreg
  have hind0 : LinearIndependent ℝ
      (![deriv (gamma false) 0, deriv sigma 0] : Fin 2 → AnnulusCoordinates) := by
    rw [linearIndependent_fin2]
    refine ⟨hsreg 0 ⟨le_rfl, hS.le⟩, ?_⟩
    intro c he
    change c • deriv sigma 0 = deriv (gamma false) 0 at he
    have hpos := N.metric.pos (gamma false 0) (deriv sigma 0) (hsreg 0 ⟨le_rfl, hS.le⟩)
    have ho := horth
    rw [← he, map_smul, smul_apply, smul_eq_mul] at ho
    have hc0 : c = 0 := (mul_eq_zero.mp ho).resolve_right hpos.ne'
    apply hreg0
    simpa only [hc0, zero_smul] using he.symm
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  obtain ⟨R, v0, vj, v1, hv0, hvj, hv1, _⟩ := m64Intrinsic_exists_three_arc_triangulation
    gamma sigma T hg hs hT hS hspeed hinj hsi hstart hend hjoin hreg htan hab has hbs
    hregAll (fun t ht => hsreg t (Ioo_subset_Icc_self ht)) hind0 hind1
    hU hV hUV hfront hfV hcompact
  exact m64Intrinsic_three_arc_region_curvature_lower_bound N R gamma sigma T hg hs
    hT hS hspeed hinj hsi hstart hend hjoin hreg htan hab has hbs hregular hreg0 horth
    hgeo hsgeo hunit hsunit habound hcircleInj hcircle hU hV hUV hfront hfV hclosure hVconn
    hinward hsub v0 vj v1 hv0 hvj hv1

end PoincareConjecture
