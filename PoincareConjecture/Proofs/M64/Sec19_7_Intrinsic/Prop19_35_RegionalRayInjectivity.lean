import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryReturnTransverse
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseReturnCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalReturnRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedJordanRegions
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalContactComparison
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_regional_ray_injOn
    (N : IntrinsicAnnulus) {K : ℝ} (hK : N.GaussianCurvatureBound K)
    (hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V)
    (hd : Disjoint U V) (hcover : U ∪ V = (frontier U)ᶜ)
    (hfront : frontier U = frontier V) (hsub : closure U ⊆ standardAnnulusDomain)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : N.metric.IsGeodesicOn gamma (Icc 0 T))
    (hT : 0 < T) (h0 : ‖gamma 0‖ = 1)
    (hinward : 0 < inner ℝ (gamma 0) (deriv gamma 0))
    (hunit : ∀ x ∈ Icc 0 T,
      N.metric.inner (gamma x) (deriv gamma x) (deriv gamma x) = 1)
    (hprefix : ∀ x ∈ Ioo 0 T, gamma x ∈ U) : InjOn gamma (Icc 0 T) := by
  by_contra hnot
  have hreg (x : ℝ) (hx : x ∈ Icc 0 T) : deriv gamma x ≠ 0 := by
    intro hz
    have hu := hunit x hx
    simp only [hz, map_zero] at hu
    norm_num at hu
  obtain ⟨s, t, hs, hst, ht, hreturn, hinj, W, Y, hW, hY, _, hpY,
      hbW, _, hdW, hcW, hfW, hfY, hkW⟩ :=
    m64Intrinsic_regular_selfintersection_region hg hreg hnot
  have htpos : 0 < t := hs.trans_lt hst
  have hgammaClosure : gamma '' Icc 0 T ⊆ closure U := by
    rw [← closure_Ioo hT.ne]
    apply (image_closure_subset_closure_image hg.continuous).trans
    apply closure_mono
    rintro _ ⟨x, hx, rfl⟩
    exact hprefix x hx
  have hfrontSub : frontier W ⊆ closure U := by
    rw [hfW]
    exact (image_mono (Icc_subset_Icc hs ht)).trans hgammaClosure
  have hWU : W ⊆ U :=
    m64Intrinsic_jordan_nested_of_frontier_subset hU hV hW hY hpV hbW hbV
      hd hdW hcover (by simpa only [hfW] using hcW) hfront hfrontSub
  have hWsub : closure W ⊆ standardAnnulusDomain := (closure_mono hWU).trans hsub
  have hnorm (x : ℝ) (hx : x ∈ Ioo 0 T) : 1 < ‖gamma x‖ :=
    (m64Intrinsic_open_region_strictly_inside_annulus hU hsub
      (gamma x) (hprefix x hx)).1
  have hind : LinearIndependent ℝ
      (![deriv gamma s, -deriv gamma t] : Fin 2 → AnnulusCoordinates) := by
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · have hs' : s = 0 := hs0.symm
      subst s
      exact m64Intrinsic_unit_boundary_return_transverse N.metric hg
        (fun x hx => hgeo x ⟨hx.1, hx.2.trans ht⟩) htpos h0
        (fun x hx => hnorm x ⟨hx.1, hx.2.trans_le ht⟩) hinward
        (fun x hx => hunit x ⟨hx.1, hx.2.trans ht⟩) hreturn
    · have hinside (x : ℝ) (hx : x ∈ Ioc 0 t) : 1 < ‖gamma x‖ := by
        rcases lt_or_eq_of_le hx.2 with hxt | rfl
        · exact hnorm x ⟨hx.1, hxt.trans_le ht⟩
        · rw [← hreturn]
          exact hnorm s ⟨hspos, hst.trans_le ht⟩
      exact m64Intrinsic_unit_interior_return_transverse N.metric hg
        (fun x hx => hgeo x ⟨hx.1, hx.2.trans ht⟩) hs hst le_rfl h0 hinside
        (fun x hx => hunit x ⟨hx.1, hx.2.trans ht⟩) hreturn
  let q : ℝ → AnnulusCoordinates := fun x => gamma (s + x)
  have hq : ContDiff ℝ ∞ q := hg.comp (contDiff_const.add contDiff_id)
  have hqd (x : ℝ) : deriv q x = deriv gamma (s + x) := by
    have h := ((hg.differentiable (by simp) (s + x)).hasDerivAt).scomp x
      ((hasDerivAt_id x).const_add s)
    have h' : HasDerivAt q (deriv gamma (s + x)) x := by
      simpa only [q, Function.comp_def, id_eq, one_smul] using! h
    exact h'.deriv
  have hqgeo : N.metric.IsGeodesicOn q (Icc 0 (t - s)) := by
    have h : N.metric.IsGeodesicOn (fun x => gamma (x + s)) (Icc 0 (t - s)) := by
      intro x hx
      apply hgeo.comp_add s
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa only [q, add_comm] using h
  have hqe : q 0 = q (t - s) := by
    simpa only [q, add_zero, show s + (t - s) = t by ring] using hreturn
  have hqi : InjOn q (Ico 0 (t - s)) := by
    intro x hx y hy heq
    have h := hinj ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ heq
    linarith
  have hqunit (x : ℝ) (hx : x ∈ Icc 0 (t - s)) :
      N.metric.inner (q x) (deriv q x) (deriv q x) = 1 := by
    rw [hqd]
    exact hunit (s + x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hqind : LinearIndependent ℝ
      (![deriv q 0, -deriv q (t - s)] : Fin 2 → AnnulusCoordinates) := by
    simpa only [hqd, add_zero, show s + (t - s) = t by ring] using hind
  have hqimage : q '' Icc 0 (t - s) = gamma '' Icc s t := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s + x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x - s, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
      change gamma (s + (x - s)) = gamma x
      congr 1
      ring
  have hclosure : closure W ∪ closure Y = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ frontier W
    · exact Or.inl (frontier_subset_closure hp)
    · have hp' : p ∈ W ∪ Y := by
        simpa only [hcW, ← hfW, mem_compl_iff] using hp
      exact hp'.elim (fun h => Or.inl (subset_closure h))
        (fun h => Or.inr (subset_closure h))
  have hlower := m64Intrinsic_transverse_geodesic_return_curvature_ge_pi
    N.connection hq (sub_pos.mpr hst) hqe hqi hqgeo hqunit hqind hW hY hdW
      (hfW.trans hqimage.symm) (hfY.trans hqimage.symm) hclosure
      hpY.isConnected.isPreconnected hkW
  have hupper := m64Intrinsic_region_gaussian_integral_le_area N hK hkW hWsub
  exact (not_lt_of_ge (hlower.trans hupper)) hsmall

end PoincareConjecture
