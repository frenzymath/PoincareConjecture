import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_OrientedContactRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TranslatedLastContactContradiction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

theorem m64Intrinsic_short_circle_last_contact_tail_impossible
    (N : IntrinsicAnnulus) {base alpha beta eta : ℝ → AnnulusCoordinates}
    (hb : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hc : ContDiff ℝ ∞ beta)
    (he : ContDiff ℝ ∞ eta) {D A B p u T c r : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hp : p ∈ Ioo 0 D) (huT : u < T)
    (hbi : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hci : InjOn beta (Icc 0 B)) (hei : InjOn eta (Icc u T))
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B) (heu : eta u = base p) (heT : eta T = alpha A)
    (hbaseA : ∀ x ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base x = alpha t → x = 0 ∧ t = 0)
    (hbaseB : ∀ x ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base x = beta t → x = D ∧ t = 0)
    (hreg : ∀ t ∈ Icc 0 D, deriv base t ≠ 0)
    (hcne : c ≠ 0) (htangent : deriv eta u = c • deriv base p)
    (horthA : N.metric.inner (base 0) (deriv base 0) (deriv alpha 0) = 0)
    (horthB : N.metric.inner (base D) (deriv base D) (deriv beta 0) = 0)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hgeoE : N.metric.IsGeodesicOn eta (Icc u T))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hunitE : ∀ t ∈ Icc u T, N.metric.inner (eta t) (deriv eta t) (deriv eta t) = 1)
    (hindA : LinearIndependent ℝ (![-deriv eta T, -deriv alpha A] :
      Fin 2 → AnnulusCoordinates))
    (hindB : LinearIndependent ℝ (![-deriv eta T, -deriv beta B] :
      Fin 2 → AnnulusCoordinates))
    (hinwardA : 0 < inner ℝ (base 0) (deriv alpha 0))
    (hinwardB : 0 < inner ℝ (base D) (deriv beta 0))
    (harcs : ∀ l ∈ Icc 0 D, ∀ v ∈ Icc 0 D, l ≤ v →
      ∃ a b : ℝ, a ≤ b ∧ b ≤ a + rampPeriod ∧
        InjOn (intrinsicAnnulusBoundary 1) (Icc a b) ∧
        base '' Icc l v = intrinsicAnnulusBoundary 1 '' Icc a b ∧
        intrinsicBoundaryLength N.metric 1 a b ≤ r)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hinside : MapsTo eta (Ioo u T) U) (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) : False := by
  have hD : 0 < D := hp.1.trans hp.2
  obtain ⟨reverse, hS, hk, hq, hz, hs, hzi, hsi, hstart, hjoin, hend, htan,
      _, hzsub, hzs, U', V', hU', hV', _, hpV', _, _, hUV', hcover', hfV',
      _, hnest, hze, hse, hfront'⟩ :=
    m64Intrinsic_exists_oriented_last_contact_region hb ha hc he hA hB hp huT hbi hai hci hei
      hstartA hstartB hmeet heu heT hbaseA hbaseB hcne htangent hU hV hpV hbV hUV
      hcover hfV hfront hinside
  let zeta : ℝ → AnnulusCoordinates := fun t => base (if reverse then D - t else t)
  let sigma := if reverse then beta else alpha
  let S := if reverse then B else A
  let q := if reverse then D - p else p
  have hzreg (t : ℝ) (ht : t ∈ Icc 0 D) : deriv zeta t ≠ 0 := by
    cases reverse
    · exact hreg t ht
    · change deriv (fun t => base (D - t)) t ≠ 0
      rw [deriv_comp_const_sub]
      exact neg_ne_zero.mpr (hreg _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hsgeo : N.metric.IsGeodesicOn sigma (Icc 0 S) := by
    cases reverse
    · exact hgeoA
    · exact hgeoB
  have hsunit : ∀ t ∈ Icc 0 S,
      N.metric.inner (sigma t) (deriv sigma t) (deriv sigma t) = 1 := by
    cases reverse
    · exact hunitA
    · exact hunitB
  have horth : N.metric.inner (zeta 0) (deriv zeta 0) (deriv sigma 0) = 0 := by
    cases reverse
    · exact horthA
    · change N.metric.inner (base (D - 0))
        (deriv (fun t => base (D - t)) 0 : AnnulusCoordinates)
        (deriv beta 0 : AnnulusCoordinates) = 0
      rw [sub_zero, deriv_comp_const_sub, sub_zero, map_neg, neg_apply, horthB, neg_zero]
  have hinward : 0 < inner ℝ (zeta 0) (deriv sigma 0) := by
    cases reverse
    · exact hinwardA
    · simpa only [zeta, sigma, if_true, sub_zero] using hinwardB
  have hind : LinearIndependent ℝ (![-deriv eta T, -deriv sigma S] :
      Fin 2 → AnnulusCoordinates) := by
    cases reverse
    · exact hindA
    · exact hindB
  have hselected : ∃ a b : ℝ, a ≤ b ∧ b ≤ a + rampPeriod ∧
      InjOn (intrinsicAnnulusBoundary 1) (Icc a b) ∧
      zeta '' Icc 0 q = intrinsicAnnulusBoundary 1 '' Icc a b ∧
      intrinsicBoundaryLength N.metric 1 a b ≤ r := by
    cases reverse
    · obtain ⟨a, b, hab, hperiod, hci, hcircle, hshort⟩ :=
        harcs 0 ⟨le_rfl, hD.le⟩ p (Ioo_subset_Icc_self hp) hp.1.le
      exact ⟨a, b, hab, hperiod, hci, hzsub.trans hcircle, hshort⟩
    · obtain ⟨a, b, hab, hperiod, hci, hcircle, hshort⟩ :=
        harcs p (Ioo_subset_Icc_self hp) D ⟨hD.le, le_rfl⟩ hp.2.le
      exact ⟨a, b, hab, hperiod, hci, hzsub.trans hcircle, hshort⟩
  obtain ⟨a, b, hab, hperiod, hcircleInj, hcircle, hshort⟩ := hselected
  have hclosure' : closure U' ∪ closure V' = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ frontier U'
    · exact Or.inl (frontier_subset_closure hz)
    · have hz' : z ∈ U' ∪ V' := by rwa [hcover']
      exact hz'.elim (fun h => Or.inl (subset_closure h)) (fun h => Or.inr (subset_closure h))
  have hqD : Icc (0 : ℝ) q ⊆ Icc 0 D := Icc_subset_Icc le_rfl hq.2.le
  exact m64Intrinsic_translated_last_contact_region_contradiction N hz hs he hq.1 hS huT hk
    (hzi.mono hqD) hsi hei hstart.symm hend hjoin
    (hzreg q (Ioo_subset_Icc_self hq)) htan hze (fun x hx => hzs x (hqD hx)) hse
    (fun t ht => hzreg t (hqD (Ioo_subset_Icc_self ht))) (hzreg 0 ⟨le_rfl, hD.le⟩)
    horth hgeoE hsgeo hunitE hsunit hind hab hcircleInj hcircle hU' hV' hUV' hfront' hfV'
    hclosure' hpV'.isConnected.isPreconnected hinward (hnest.trans hsub)
    hK hturn harea hbudget hperiod hshort

end PoincareConjecture
