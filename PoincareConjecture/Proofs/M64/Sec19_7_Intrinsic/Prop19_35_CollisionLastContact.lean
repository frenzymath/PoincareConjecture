import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CollisionSideAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SmoothLastContact










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix ENNReal Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_collision_minimizer_smooth_last_contact
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {base alpha beta : ℝ → AnnulusCoordinates}
    (hb : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hc : ContDiff ℝ ∞ beta)
    {D A B p₀ : ℝ} (hD : 0 < D) (hA : 0 < A) (hB : 0 < B) (hp₀ : p₀ ∈ Ioo 0 D)
    (hbi : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hci : InjOn beta (Icc 0 B))
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hregBase : ∀ t ∈ Ioo 0 D, deriv base t ≠ 0)
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
    (hg0 : gamma 0 = base p₀) (hgL : gamma L = alpha A)
    (hconf : MapsTo gamma (Icc 0 L) (closure U))
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma s → tau 1 = gamma t → MapsTo tau (Icc 0 1) (closure U) →
          ENNReal.ofReal (t - s) ≤ m64IntrinsicCurveVariation G tau 0 1)
    (hcontact : ∃ t ∈ Ioo 0 L, gamma t ∈ base '' Icc 0 D) :
    ∃ u p c : ℝ, ∃ eta : ℝ → AnnulusCoordinates,
      u ∈ Ioo 0 L ∧ p ∈ Ioo 0 D ∧ c ≠ 0 ∧
      ContDiff ℝ ∞ eta ∧ EqOn eta gamma (Icc u L) ∧ InjOn eta (Icc u L) ∧
      eta u = base p ∧ eta L = alpha A ∧ MapsTo eta (Ioo u L) U ∧
      G.IsGeodesicOn eta (Icc u L) ∧ deriv eta u = c • deriv base p ∧
      (∀ t ∈ Icc u L, G.tangentNorm (eta t) (deriv eta t) = 1) ∧
      (∀ t ∈ Icc u L, deriv eta t ≠ 0) := by
  have hside := m64Intrinsic_constrained_minimizer_avoids_collision_sides G hb ha hc
    hD hA hB hp₀ hbi hai hci hstartA hstartB hmeet hbaseA hbaseB hsides
    hregA hregB hgeoA hgeoB hindA hindB hnormA hnormB hinwardA hinwardB
    hU hV hdisj hfU hfV hK hsub hgamma hginj hg0 hgL hconf hlip hmin
  have hcorners (t : ℝ) (ht : t ∈ Ioo 0 L) : gamma t ≠ base 0 ∧ gamma t ≠ base D := by
    constructor
    · intro heq
      exact hside t ht (Or.inl ⟨0, ⟨le_rfl, hA.le⟩, hstartA.symm.trans heq.symm⟩)
    · intro heq
      exact hside t ht (Or.inr ⟨0, ⟨le_rfl, hB.le⟩, hstartB.symm.trans heq.symm⟩)
  have hseparate (p : ℝ) (hp : p ∈ Ioo 0 D) :
      base p ∉ alpha '' Icc 0 A ∪ beta '' Icc 0 B := by
    rintro (⟨t, ht, heq⟩ | ⟨t, ht, heq⟩)
    · exact hp.1.ne' (hbaseA p (Ioo_subset_Icc_self hp) t ht heq.symm).1
    · exact hp.2.ne (hbaseB p (Ioo_subset_Icc_self hp) t ht heq.symm).1
  have hend : gamma L ∉ base '' Icc 0 D := by
    rintro ⟨p, hp, heq⟩
    exact hA.ne' (hbaseA p hp A ⟨hA.le, le_rfl⟩ (heq.trans hgL)).2
  obtain ⟨u, p, c, eta, hu, hp, hup, hcne, heta, heq, hei, heinside, hegeo,
      hederiv, heunit, hereg⟩ :=
    m64Intrinsic_constrained_minimizer_smooth_last_base_contact G hb hbi hregBase
      ((isCompact_Icc.image ha.continuous).union (isCompact_Icc.image hc.continuous))
      hseparate hU hV hdisj hfU hfV hK hgamma hginj hconf hlip hmin hside hcorners hend hcontact
  exact ⟨u, p, c, eta, hu, hp, hcne, heta, heq, hei,
    (heq (left_mem_Icc.mpr hu.2.le)).trans hup,
    (heq (right_mem_Icc.mpr hu.2.le)).trans hgL, heinside, hegeo, hederiv, heunit, hereg⟩

end PoincareConjecture
