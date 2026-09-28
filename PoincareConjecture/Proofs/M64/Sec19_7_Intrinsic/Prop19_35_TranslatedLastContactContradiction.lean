import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConstructedNoShortThreeArcRegion





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture







theorem m64Intrinsic_translated_last_contact_region_contradiction
    (N : IntrinsicAnnulus) {base sigma eta : ℝ → AnnulusCoordinates}
    (hb : ContDiff ℝ ∞ base) (hs : ContDiff ℝ ∞ sigma) (he : ContDiff ℝ ∞ eta)
    {q S u T c : ℝ} (hq : 0 < q) (hS : 0 < S) (huT : u < T) (hc : 0 < c)
    (hbi : InjOn base (Icc 0 q)) (hsi : InjOn sigma (Icc 0 S))
    (hei : InjOn eta (Icc u T))
    (hstart : sigma 0 = base 0) (hend : sigma S = eta T) (hjoin : base q = eta u)
    (hregq : deriv base q ≠ 0) (htan : deriv eta u = c • deriv base q)
    (hbaseTail : ∀ x ∈ Icc 0 q, ∀ t ∈ Icc u T, base x = eta t → x = q ∧ t = u)
    (hbaseSide : ∀ x ∈ Icc 0 q, ∀ s ∈ Icc 0 S, base x = sigma s → x = 0 ∧ s = 0)
    (hsideTail : ∀ s ∈ Icc 0 S, ∀ t ∈ Icc u T, sigma s = eta t → s = S ∧ t = T)
    (hregular : ∀ t ∈ Ioo 0 q, deriv base t ≠ 0) (hreg0 : deriv base 0 ≠ 0)
    (horth : N.metric.inner (base 0) (deriv base 0) (deriv sigma 0) = 0)
    (hegeo : N.metric.IsGeodesicOn eta (Icc u T))
    (hsgeo : N.metric.IsGeodesicOn sigma (Icc 0 S))
    (heunit : ∀ t ∈ Icc u T, N.metric.inner (eta t) (deriv eta t) (deriv eta t) = 1)
    (hsunit : ∀ t ∈ Icc 0 S, N.metric.inner (sigma t) (deriv sigma t) (deriv sigma t) = 1)
    (hind : LinearIndependent ℝ (![-deriv eta T, -deriv sigma S] :
      Fin 2 → AnnulusCoordinates))
    {a b : ℝ} (hab : a ≤ b)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    (hcircle : base '' Icc 0 q = intrinsicAnnulusBoundary 1 '' Icc a b)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 q ∪ (sigma '' Icc 0 S ∪ eta '' Icc u T))
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hinward : 0 < inner ℝ (base 0) (deriv sigma 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta r mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hperiod : b ≤ a + rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ r) : False := by
  let tail (t : ℝ) := eta (t + u)
  let gamma (e : Bool) := if e then tail else base
  let L (e : Bool) := if e then T - u else q
  have hparam {t : ℝ} (ht : t ∈ Icc 0 (T - u)) : t + u ∈ Icc u T :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htd (t : ℝ) : deriv tail t = deriv eta (t + u) := by
    change deriv (fun t => eta (t + u)) t = _
    rw [deriv_comp_add_const]
  have htimage : tail '' Icc 0 (T - u) = eta '' Icc u T := by
    change (eta ∘ fun t => t + u) '' Icc 0 (T - u) = _
    rw [image_comp, image_add_const_Icc]
    simp only [zero_add, sub_add_cancel]
  have htgeo : N.metric.IsGeodesicOn tail (Icc 0 (T - u)) := by
    intro t ht
    exact hegeo.comp_add u t (hparam ht)
  have htunit (t : ℝ) (ht : t ∈ Icc 0 (T - u)) :
      N.metric.inner (tail t) (deriv tail t) (deriv tail t) = 1 := by
    change N.metric.inner (eta (t + u)) (deriv tail t : AnnulusCoordinates)
      (deriv tail t : AnnulusCoordinates) = 1
    rw [htd]
    exact heunit (t + u) (hparam ht)
  have hg (e : Bool) : ContDiff ℝ ∞ (gamma e) := by
    cases e
    · exact hb
    · exact he.comp (contDiff_id.add contDiff_const)
  have hL (e : Bool) : 0 < L e := by
    cases e
    · exact hq
    · exact sub_pos.mpr huT
  have hgi (e : Bool) : InjOn (gamma e) (Icc 0 (L e)) := by
    cases e
    · exact hbi
    · intro s hs t ht heq
      exact add_right_cancel (hei (hparam hs) (hparam ht) heq)
  have hbaseTail' : ∀ x ∈ Icc 0 q, ∀ t ∈ Icc 0 (T - u),
      base x = tail t → x = q ∧ t = 0 := by
    intro x hx t ht heq
    have hh := hbaseTail x hx (t + u) (hparam ht) heq
    exact ⟨hh.1, by linarith [hh.2]⟩
  have htailSide : ∀ t ∈ Icc 0 (T - u), ∀ s ∈ Icc 0 S,
      tail t = sigma s → t = T - u ∧ s = S := by
    intro t ht s hs heq
    have hh := hsideTail s hs (t + u) (hparam ht) heq.symm
    exact ⟨by linarith [hh.2], hh.1⟩
  have hfront' : frontier U = gamma false '' Icc 0 (L false) ∪
      gamma true '' Icc 0 (L true) ∪ sigma '' Icc 0 S := by
    change frontier U = base '' Icc 0 q ∪ tail '' Icc 0 (T - u) ∪ sigma '' Icc 0 S
    rw [htimage]
    exact hfront.trans (by ac_rfl)
  have hind' : LinearIndependent ℝ (![-deriv tail (T - u), -deriv sigma S] :
      Fin 2 → AnnulusCoordinates) := by
    simpa only [htd, sub_add_cancel] using hind
  exact m64Intrinsic_constructed_no_short_three_arc_region N gamma sigma L hg hs hL hS hc
    hgi hsi hstart (by simpa only [gamma, tail, L, if_true, sub_add_cancel] using hend)
    (by simpa only [gamma, tail, L, if_true, Bool.false_eq_true, if_false, zero_add] using hjoin)
    hregq (by simpa only [gamma, L, if_true, Bool.false_eq_true, if_false, htd, zero_add]
      using htan) hbaseTail' hbaseSide htailSide hregular hreg0 horth htgeo hsgeo htunit hsunit
    hind' hab hcircleInj hcircle hU hV hUV hfront' hfV hclosure hVconn hinward hsub
    hK hturn harea hbudget hperiod hshort

end PoincareConjecture
