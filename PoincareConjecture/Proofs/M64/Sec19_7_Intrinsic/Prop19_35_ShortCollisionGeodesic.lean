import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactMinimizerGeodesic
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BaseToVertexMinimizer





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold ENNReal

namespace PoincareConjecture








theorem m64Intrinsic_exists_short_collision_geodesic
    (N : IntrinsicAnnulus) {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b A B p r : ℝ} (hab : a < b) (hA : 0 < A) (hB : 0 < B) (hp : p ∈ Ioo a b)
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
    (hperiod : b - a < rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfV : frontier V = frontier U)
    (hfront : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪
      (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hsub : closure U ⊆ standardAnnulusDomain)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    ∃ (eta : ℝ → AnnulusCoordinates) (T : ℝ),
      0 < T ∧ T ≤ intrinsicBoundaryLength N.metric 1 a b / 2 + max A B ∧
      ContDiff ℝ ∞ eta ∧ eta 0 = intrinsicAnnulusBoundary 1 p ∧ eta T = alpha A ∧
      MapsTo eta (Icc 0 T) (closure U) ∧ MapsTo eta (Ioo 0 T) U ∧
      InjOn eta (Icc 0 T) ∧ N.metric.IsGeodesicOn eta (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, N.metric.inner (eta t) (deriv eta t) (deriv eta t) = 1 := by
  let base : ℝ → AnnulusCoordinates := fun t => intrinsicAnnulusBoundary 1 (a + t)
  have hD : 0 < b - a := sub_pos.mpr hab
  have hparam : base = fun t => intrinsicAnnulusBoundary 1 (a + 1 * t) := by
    simp only [base, one_mul]
  have hc0 : base 0 = intrinsicAnnulusBoundary 1 a := by simp only [base, add_zero]
  have hcD : base (b - a) = intrinsicAnnulusBoundary 1 b := by
    simp only [base, add_sub_cancel]
  have hbaseA : base 0 = alpha 0 := hc0.trans ha0.symm
  have hbaseB : base (b - a) = beta 0 := hcD.trans hb0.symm
  have hci : InjOn base (Icc 0 (b - a)) := by
    intro s hs t ht hst
    have he := m64Intrinsic_boundary_injOn_short_arc hperiod
      (show a + s ∈ Icc a b from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (show a + t ∈ Icc a b from ⟨by linarith [ht.1], by linarith [ht.2]⟩) hst
    exact add_left_cancel he
  have hbaseNorm (t : ℝ) : ‖base t‖ = 1 := m64Intrinsic_inner_boundary_norm _
  have hca : ∀ s ∈ Icc 0 (b - a), ∀ t ∈ Icc 0 A,
      base s = alpha t → s = 0 ∧ t = 0 := by
    intro s hs t ht heq
    have ht0 : t = 0 := by
      by_contra hn
      have hnrm := haInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm hn), ht.2⟩
      rw [← heq, hbaseNorm] at hnrm
      exact (lt_irrefl (1 : ℝ)) hnrm
    exact ⟨hci hs ⟨le_rfl, hD.le⟩ (by rw [heq, ht0, hbaseA]), ht0⟩
  have hcb : ∀ s ∈ Icc 0 (b - a), ∀ t ∈ Icc 0 B,
      base s = beta t → s = b - a ∧ t = 0 := by
    intro s hs t ht heq
    have ht0 : t = 0 := by
      by_contra hn
      have hnrm := hbInterior t ⟨lt_of_le_of_ne ht.1 (Ne.symm hn), ht.2⟩
      rw [← heq, hbaseNorm] at hnrm
      exact (lt_irrefl (1 : ℝ)) hnrm
    exact ⟨hci hs ⟨hD.le, le_rfl⟩ (by rw [heq, ht0, hbaseB]), ht0⟩
  have himage : base '' Icc 0 (b - a) = intrinsicAnnulusBoundary 1 '' Icc a b := by
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨a + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    · rintro z ⟨t, ht, rfl⟩
      refine ⟨t - a, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      simp only [base, add_sub_cancel]
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  have hsideA : MapsTo alpha (Icc 0 A) (closure U) := by
    intro t ht
    apply frontier_subset_closure
    rw [hfront]
    exact Or.inr (Or.inl (mem_image_of_mem alpha ht))
  have hsideB : MapsTo beta (Icc 0 B) (closure U) := by
    intro t ht
    apply frontier_subset_closure
    rw [hfront]
    exact Or.inr (Or.inr (mem_image_of_mem beta ht))
  have hcircle : MapsTo (intrinsicAnnulusBoundary 1) (Icc a b) (closure U) := by
    intro t ht
    apply frontier_subset_closure
    rw [hfront]
    exact Or.inl (mem_image_of_mem _ ht)
  obtain ⟨gamma, T, hT, hbound, hc, hg0, hgT, hconf, hgi, hlip, _, _, _, hmin⟩ :=
    m64Intrinsic_exists_short_base_to_vertex_minimizer N hcompact (Ioo_subset_Icc_self hp)
      hA.le hB.le ha hb hunitA hunitB ha0 hb0 hmeet hsideA hsideB hcircle
  have hTpos : 0 < T := by
    apply lt_of_le_of_ne hT
    intro he
    have hn := haInterior A ⟨hA, le_rfl⟩
    rw [← hgT, ← he, hg0, m64Intrinsic_inner_boundary_norm] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  obtain ⟨_, hd, _, _⟩ := m64Intrinsic_affine_inner_circle_properties N a 1 one_ne_zero
  have hderiv (t : ℝ) : deriv base t = deriv (intrinsicAnnulusBoundary 1) (a + t) := by
    simpa only [one_mul, one_smul] using hd t
  have horth0 : N.metric.inner (base 0)
      (deriv base 0 : AnnulusCoordinates) (deriv alpha 0 : AnnulusCoordinates) = 0 := by
    rw [hc0, hderiv, add_zero]
    exact horthA
  have horthD : N.metric.inner (base (b - a)) (deriv base (b - a) : AnnulusCoordinates)
      (deriv beta 0 : AnnulusCoordinates) = 0 := by
    rw [hcD, hderiv, add_sub_cancel]
    exact horthB
  have hinside := m64Intrinsic_affine_collision_minimizer_interior N ha hb hparam
    one_ne_zero hD hA hB
    (show p - a ∈ Ioo 0 (b - a) from ⟨by linarith [hp.1], by linarith [hp.2]⟩)
    hci hai hbi hbaseA hbaseB hmeet hca hcb hsides horth0 horthD
    hgeoA hgeoB hunitA hunitB haInterior hbInterior
    (hc0.symm ▸ hinwardA) (hcD.symm ▸ hinwardB)
    (by simpa only [one_mul, abs_of_pos hD] using hperiod)
    (by simpa only [one_mul, add_sub_cancel, min_eq_left hab.le,
      max_eq_right hab.le] using hshort)
    hU hV hpV hbV hUV hcover hfV (by rw [himage]; exact hfront) hsub
    hc hgi (by simpa only [base, add_sub_cancel] using hg0) hgT hconf hlip hmin
    hK hturn harea hbudget
  obtain ⟨eta, he, heq, hegeo, heunit, _, _, _⟩ :=
    m64Intrinsic_constrained_minimizer_smooth_unit_geodesic N.metric
      hU hcompact hTpos hc hinside hlip hmin
  refine ⟨eta, T, hTpos, hbound, he, (heq ⟨le_rfl, hT⟩).trans hg0,
    (heq ⟨hT, le_rfl⟩).trans hgT, ?_, ?_, ?_, hegeo, heunit⟩
  · intro t ht
    rw [heq ht]
    exact hconf ht
  · intro t ht
    rw [heq (Ioo_subset_Icc_self ht)]
    exact hinside ht
  · intro s hs t ht hst
    apply hgi hs ht
    rwa [← heq hs, ← heq ht]

end PoincareConjecture
