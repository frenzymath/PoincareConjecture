import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCollisionTransverse
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleConvexity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AffineCircleSubarcs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

theorem m64Intrinsic_normal_collision_convex_corner
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b A B r : ℝ} (hab : a < b) (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b) (hmeet : alpha A = beta B)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (horthA : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (deriv (intrinsicAnnulusBoundary 1) a) (deriv alpha 0) = 0)
    (horthB : N.metric.inner (intrinsicAnnulusBoundary 1 b)
      (deriv (intrinsicAnnulusBoundary 1) b) (deriv beta 0) = 0)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (haInterior : ∀ t ∈ Ioc 0 A, 1 < ‖alpha t‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖)
    (hinwardA : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (deriv alpha 0))
    (hinwardB : 0 < inner ℝ (intrinsicAnnulusBoundary 1 b) (deriv beta 0))
    (hperiod : b - a < rampPeriod) (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K) (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha A) ∧ phi (alpha A) = 0 ∧
      L.symm (1, 0) = -deriv alpha A ∧ L.symm (0, 1) = -deriv beta B ∧
      (∀ᶠ z in 𝓝 (alpha A), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) := by
  let base : ℝ → AnnulusCoordinates := fun t => intrinsicAnnulusBoundary 1 (a + t)
  have hD : 0 < b - a := sub_pos.mpr hab
  obtain ⟨hc', hd', hn', hr'⟩ := m64Intrinsic_affine_inner_circle_properties N a 1 one_ne_zero
  have hc : ContDiff ℝ ∞ base := by simpa only [base, one_mul] using hc'
  have hderiv (t : ℝ) : deriv base t = deriv (intrinsicAnnulusBoundary 1) (a + t) := by
    simpa only [base, one_mul, one_smul] using hd' t
  have hnorm (t : ℝ) : ‖base t‖ = 1 := by simpa only [base, one_mul] using hn' t
  have hregular (t : ℝ) : deriv base t ≠ 0 := by simpa only [base, one_mul] using hr' t
  have hc0 : base 0 = intrinsicAnnulusBoundary 1 a := by simp only [base, add_zero]
  have hcD : base (b - a) = intrinsicAnnulusBoundary 1 b := by simp only [base, add_sub_cancel]
  have hstartA : base 0 = alpha 0 := hc0.trans ha0.symm
  have hstartB : base (b - a) = beta 0 := hcD.trans hb0.symm
  have hcircle := m64Intrinsic_boundary_injOn_short_arc hperiod
  have hci : InjOn base (Icc 0 (b - a)) := by
    intro s hs t ht heq
    exact add_left_cancel (hcircle
      (show a + s ∈ Icc a b from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (show a + t ∈ Icc a b from ⟨by linarith [ht.1], by linarith [ht.2]⟩) heq)
  have hca : ∀ s ∈ Icc 0 (b - a), ∀ t ∈ Icc 0 A,
      base s = alpha t → s = 0 ∧ t = 0 := by
    intro s hs t ht heq
    have ht0 : t = 0 := by
      by_contra hn
      have h := haInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm hn), ht.2⟩
      rw [← heq, hnorm] at h
      exact (lt_irrefl (1 : ℝ)) h
    exact ⟨hci hs ⟨le_rfl, hD.le⟩ (by rw [heq, ht0, hstartA]), ht0⟩
  have hcb : ∀ s ∈ Icc 0 (b - a), ∀ t ∈ Icc 0 B,
      base s = beta t → s = b - a ∧ t = 0 := by
    intro s hs t ht heq
    have ht0 : t = 0 := by
      by_contra hn
      have h := hbInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm hn), ht.2⟩
      rw [← heq, hnorm] at h
      exact (lt_irrefl (1 : ℝ)) h
    exact ⟨hci hs ⟨hD.le, le_rfl⟩ (by rw [heq, ht0, hstartB]), ht0⟩
  have himage : base '' Icc 0 (b - a) = intrinsicAnnulusBoundary 1 '' Icc a b := by
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨a + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t - a, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        by simp only [base, add_sub_cancel]⟩
  have hclosure : closure U ∪ closure V = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ frontier U
    · exact Or.inl (frontier_subset_closure hz)
    · have hz' : z ∈ U ∪ V := by rwa [hcover]
      exact hz'.elim (fun h => Or.inl (subset_closure h)) (fun h => Or.inr (subset_closure h))
  have hind := m64Intrinsic_short_normal_collision_transverse N ha hb hA hB hai hbi ha0 hb0
    haInterior hbInterior hgeoA hgeoB (hunitA 0 ⟨le_rfl, hA.le⟩)
      (hunitB 0 ⟨le_rfl, hB.le⟩) horthA horthB hinwardA hmeet hsides
      (by simpa only [abs_of_pos hD] using hperiod) hU hV hUV
      (by simpa only [min_eq_left hab.le, max_eq_right hab.le] using hfront)
      hfV hclosure hpV hsub hK hturn harea hbudget
      (by simpa only [min_eq_left hab.le, max_eq_right hab.le] using hshort)
  have hturn' := hturn a b hab.le (by linarith only [hperiod]) hshort
  have harea' := mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
  have hbudget' : max K 0 * intrinsicAnnulusArea N.metric +
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b < Real.pi := by
    linarith [Real.pi_pos]
  apply m64Intrinsic_small_triangle_terminal_convex_coordinates N hc ha hb hD hA hB
    hci hai hbi (fun t _ => hregular t) hstartA hstartB hmeet hca hcb hsides
    (by rw [hc0, hderiv, add_zero]; exact horthA)
    (by rw [hcD, hderiv, add_sub_cancel]; exact horthB)
    hgeoA hgeoB hunitA hunitB hind hab.le hcircle himage hU hV hUV
    (by rw [himage]; exact hfront) hfV hclosure hpV
    (hc0.symm ▸ hinwardA) (hcD.symm ▸ hinwardB) hsub hK hbudget'

end PoincareConjecture
