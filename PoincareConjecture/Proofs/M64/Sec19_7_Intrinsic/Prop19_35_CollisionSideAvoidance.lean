import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BaseCornerAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicSideAvoidance










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix ENNReal Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_constrained_minimizer_avoids_collision_sides
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {base alpha beta : ℝ → AnnulusCoordinates}
    (hb : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hc : ContDiff ℝ ∞ beta)
    {D A B p : ℝ} (hD : 0 < D) (hA : 0 < A) (hB : 0 < B) (hp : p ∈ Ioo 0 D)
    (hbi : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hci : InjOn beta (Icc 0 B))
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hregA : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hregB : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hgeoA : G.IsGeodesicOn alpha (Ioo 0 A)) (hgeoB : G.IsGeodesicOn beta (Ioo 0 B))
    (hindA : LinearIndependent ℝ (![deriv base 0, deriv alpha 0] : Fin 2 → AnnulusCoordinates))
    (hindB : LinearIndependent ℝ (![-deriv base D, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hnormA : ‖base 0‖ = 1) (hnormB : ‖base D‖ = 1)
    (hinwardA : 0 < inner ℝ (base 0) (deriv alpha 0))
    (hinwardB : 0 < inner ℝ (base D) (deriv beta 0))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V)
    (hfU : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U) (hK : IsCompact (closure U))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hgamma : ContinuousOn gamma (Icc 0 L)) (hginj : InjOn gamma (Icc 0 L))
    (hg0 : gamma 0 = base p) (hgL : gamma L = alpha A)
    (hconf : MapsTo gamma (Icc 0 L) (closure U))
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma s → tau 1 = gamma t → MapsTo tau (Icc 0 1) (closure U) →
        ENNReal.ofReal (t - s) ≤ m64IntrinsicCurveVariation G tau 0 1) :
    ∀ u ∈ Ioo 0 L, gamma u ∉ alpha '' Icc 0 A ∪ beta '' Icc 0 B := by
  have hcompactBase : IsCompact (base '' Icc 0 D) := isCompact_Icc.image hb.continuous
  have hcompactA : IsCompact (alpha '' Icc 0 A) := isCompact_Icc.image ha.continuous
  have hcompactB : IsCompact (beta '' Icc 0 B) := isCompact_Icc.image hc.continuous
  have hzeroB : base 0 ∉ beta '' Icc 0 B := by
    rintro ⟨t, ht, heq⟩
    exact hD.ne (hbaseB 0 ⟨le_rfl, hD.le⟩ t ht heq.symm).1
  have hendA : base D ∉ alpha '' Icc 0 A := by
    rintro ⟨t, ht, heq⟩
    exact hD.ne' (hbaseA D ⟨hD.le, le_rfl⟩ t ht heq.symm).1
  have hcornerA (u : ℝ) (hu : u ∈ Ioo 0 L) : gamma u ≠ alpha 0 := by
    rw [← hstartA]
    apply m64Intrinsic_constrained_minimizer_avoids_annular_base_corner G hb ha hD hA
      hbi hai hstartA.symm hindA hcompactB hzeroB hU hV hdisj
      (by simpa only [union_assoc] using hfU) hfV hnormA hinwardA hsub
      hgamma hconf hlip hmin hu
  let reverseBase := fun t : ℝ => base (D - t)
  have hr : ContDiff ℝ ∞ reverseBase := hb.comp (contDiff_const.sub contDiff_id)
  have hri : InjOn reverseBase (Icc 0 D) := by
    intro s hs t ht heq
    have hh := hbi (show D - s ∈ Icc 0 D from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (show D - t ∈ Icc 0 D from ⟨by linarith [ht.2], by linarith [ht.1]⟩) heq
    linarith
  have hrimage : reverseBase '' Icc 0 D = base '' Icc 0 D := by
    change (base ∘ fun t => D - t) '' Icc 0 D = _
    rw [image_comp, image_const_sub_Icc]
    simp only [sub_self, sub_zero]
  have hrzero : reverseBase 0 = base D := by simp only [reverseBase, sub_zero]
  have hrderiv : deriv reverseBase 0 = -deriv base D := by
    have hd : HasDerivAt base (deriv base D) (D - 0) := by
      simpa only [sub_zero] using (hb.differentiable (by simp) D).hasDerivAt
    have hh := hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_sub D)
    simpa only [reverseBase, Function.comp_def, id_eq, neg_one_smul] using hh.deriv
  have hcornerB (u : ℝ) (hu : u ∈ Ioo 0 L) : gamma u ≠ beta 0 := by
    rw [← hstartB, ← hrzero]
    apply m64Intrinsic_constrained_minimizer_avoids_annular_base_corner G hr hc hD hB
      hri hci (by rw [hrzero]; exact hstartB.symm)
      (by simpa only [hrderiv] using hindB) hcompactA
      (by simpa only [hrzero] using hendA) hU hV hdisj
      (by simpa only [hrimage, union_assoc, union_left_comm, union_comm] using hfU)
      hfV (by simpa only [hrzero] using hnormB)
      (by simpa only [hrzero] using hinwardB) hsub hgamma hconf hlip hmin hu
  have havoidA : ∀ u ∈ Ioo 0 L, gamma u ∉ alpha '' Icc 0 A := by
    apply m64Intrinsic_constrained_minimizer_avoids_geodesic_side G ha hai hregA hgeoA
      (hcompactBase.union hcompactB) _ hU hV hdisj
      (by simpa only [union_assoc, union_left_comm, union_comm] using hfU) hfV
      hK hgamma hginj hconf hlip hmin _ hgL hcornerA
    · intro t ht hmem
      rcases hmem with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
      · exact ht.1.ne' (hbaseA s hs t (Ioo_subset_Icc_self ht) heq).2
      · exact ht.2.ne (hsides t (Ioo_subset_Icc_self ht) s hs heq.symm).1
    · rintro ⟨t, ht, heq⟩
      exact hp.1.ne' (hbaseA p (Ioo_subset_Icc_self hp) t ht (hg0.symm.trans heq.symm)).1
  have havoidB : ∀ u ∈ Ioo 0 L, gamma u ∉ beta '' Icc 0 B := by
    apply m64Intrinsic_constrained_minimizer_avoids_geodesic_side G hc hci hregB hgeoB
      (hcompactBase.union hcompactA) _ hU hV hdisj
      (by simpa only [union_assoc, union_left_comm, union_comm] using hfU) hfV
      hK hgamma hginj hconf hlip hmin _ (hgL.trans hmeet) hcornerB
    · intro t ht hmem
      rcases hmem with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
      · exact ht.1.ne' (hbaseB s hs t (Ioo_subset_Icc_self ht) heq).2
      · exact ht.2.ne (hsides s hs t (Ioo_subset_Icc_self ht) heq).2
    · rintro ⟨t, ht, heq⟩
      exact hp.2.ne (hbaseB p (Ioo_subset_Icc_self hp) t ht (hg0.symm.trans heq.symm)).1
  intro u hu hmem
  exact hmem.elim (havoidA u hu) (havoidB u hu)

end PoincareConjecture
