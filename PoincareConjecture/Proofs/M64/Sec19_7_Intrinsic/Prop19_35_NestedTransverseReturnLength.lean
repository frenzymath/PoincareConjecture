import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RawInnerNormalReturn
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedReturnRegion












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture





theorem m64Intrinsic_nested_transverse_return_length_gt
    (N : IntrinsicAnnulus)
    {U V : Set AnnulusCoordinates}
    (hU : IsOpen U) (hV : IsOpen V) (hpV : IsPreconnected V)
    (hbV : ¬ Bornology.IsBounded V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {a b x y T : ℝ}
    (hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hperiod : b - a < rampPeriod) (hT : 0 < T)
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    (hgi : InjOn gamma (Icc 0 T))
    (h0 : gamma 0 = intrinsicAnnulusBoundary 1 x)
    (h1 : gamma T = intrinsicAnnulusBoundary 1 y)
    (hprefix : ∀ t ∈ Ioo 0 T, gamma t ∈ U)
    (hgeo : N.metric.IsGeodesicOn gamma (Icc 0 T))
    (hunit0 : N.metric.inner (gamma 0) (deriv gamma 0) (deriv gamma 0) = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary 1 x)
      (deriv (intrinsicAnnulusBoundary 1) x) (deriv gamma 0) = 0)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 x) (deriv gamma 0))
    (hterminal : LinearIndependent ℝ
      (![deriv (intrinsicAnnulusBoundary 1) y, deriv gamma T] :
        Fin 2 → AnnulusCoordinates))
    {K delta r mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    r < intrinsicBoundaryLength N.metric 1 (min x y) (max x y) := by
  have hxy : x ≠ y := by
    intro heq
    have hends : gamma 0 = gamma T :=
      h0.trans ((congrArg (intrinsicAnnulusBoundary 1) heq).trans h1.symm)
    exact hT.ne (hgi ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hends)
  have hminmax : min x y < max x y := min_lt_max.mpr hxy
  have hwidth : max x y - min x y < rampPeriod :=
    (sub_le_sub (max_le hx.2 hy.2) (le_min hx.1 hy.1)).trans_lt hperiod
  have hrawPeriod : |y - x| < rampPeriod := by
    simpa only [max_sub_min_eq_abs, abs_sub_comm] using hwidth
  have hinside : ∀ t ∈ Ioo 0 T, 1 < ‖gamma t‖ := by
    intro t ht
    exact (m64Intrinsic_open_region_strictly_inside_annulus hU hsub
      (gamma t) (hprefix t ht)).1
  have hends :
      (gamma 0 = intrinsicAnnulusBoundary 1 (min x y) ∧
        gamma T = intrinsicAnnulusBoundary 1 (max x y)) ∨
      (gamma 0 = intrinsicAnnulusBoundary 1 (max x y) ∧
        gamma T = intrinsicAnnulusBoundary 1 (min x y)) := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact Or.inl ⟨h0, h1⟩
    · rw [min_eq_right h, max_eq_left h]
      exact Or.inr ⟨h0, h1⟩
  obtain ⟨W, Y, hW, hY, _, hpY, _, _, hdW, hcW, hfW, hfY, _, _, _, hsubW⟩ :=
    m64Intrinsic_exists_nested_inner_return_region hU hV hpV hbV hdisj hcover hfront
      hsub hcircle (le_min hx.1 hy.1) hminmax (max_le hx.2 hy.2) hperiod hT
      hg.continuous hgi hends hprefix
  have hclosed : closure W ∪ closure Y = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ frontier W
    · exact Or.inl (frontier_subset_closure hp)
    · have hp' : p ∈ W ∪ Y := by
        simpa only [hcW, ← hfW, mem_compl_iff] using hp
      exact hp'.elim (fun h => Or.inl (subset_closure h))
        (fun h => Or.inr (subset_closure h))
  by_contra hshort
  exact m64Intrinsic_no_short_transverse_inner_return N hg hT hgi h0 h1 hinside
    hgeo hunit0 horth hinward hterminal hrawPeriod hW hY hdW hfW
    (hfY.trans hfW.symm) hclosed hpY.isConnected.isPreconnected hsubW
    hK hturn harea hbudget (le_of_not_gt hshort)

end PoincareConjecture
