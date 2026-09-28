import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CollisionLastContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleConvexity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LastTailTransverse
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NoLastContactTail





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix ENNReal

namespace PoincareConjecture








theorem m64Intrinsic_short_collision_minimizer_avoids_base
    (N : IntrinsicAnnulus) {base alpha beta : ℝ → AnnulusCoordinates}
    (hb : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hc : ContDiff ℝ ∞ beta)
    {D A B p0 r : ℝ} (hD : 0 < D) (hA : 0 < A) (hB : 0 < B) (hp0 : p0 ∈ Ioo 0 D)
    (hbi : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hci : InjOn beta (Icc 0 B))
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hreg : ∀ t ∈ Icc 0 D, deriv base t ≠ 0)
    (horthA : N.metric.inner (base 0) (deriv base 0) (deriv alpha 0) = 0)
    (horthB : N.metric.inner (base D) (deriv base D) (deriv beta 0) = 0)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hindT : LinearIndependent ℝ (![-deriv alpha A, -deriv beta B] :
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
    (hsub : closure U ⊆ standardAnnulusDomain)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hgamma : ContinuousOn gamma (Icc 0 T)) (hgi : InjOn gamma (Icc 0 T))
    (hg0 : gamma 0 = base p0) (hgT : gamma T = alpha A)
    (hconf : MapsTo gamma (Icc 0 T) (closure U))
    (hlip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      N.metric.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma s → tau 1 = gamma t → MapsTo tau (Icc 0 1) (closure U) →
          ENNReal.ofReal (t - s) ≤ m64IntrinsicCurveVariation N.metric tau 0 1)
    {K delta mu : ℝ} (hK : N.GaussianCurvatureBound K)
    (hturn : N.SmallBoundaryTurning delta r)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    ∀ t ∈ Ioo 0 T, gamma t ∉ base '' Icc 0 D := by
  intro t ht hcontact
  obtain ⟨a, b, hab, hperiod, hcircleInj, hcircle, hshort⟩ :=
    harcs 0 ⟨le_rfl, hD.le⟩ D ⟨hD.le, le_rfl⟩ hD.le
  have hnorm (s : ℝ) (hs : s ∈ Icc 0 D) : ‖base s‖ = 1 := by
    have hp : base s ∈ intrinsicAnnulusBoundary 1 '' Icc a b :=
      hcircle ▸ mem_image_of_mem base hs
    obtain ⟨z, _, hz⟩ := hp
    rw [← hz, m64Intrinsic_inner_boundary_norm]
  have hregA (s : ℝ) (hs : s ∈ Icc 0 A) : deriv alpha s ≠ 0 := by
    intro hz
    have hu := hunitA s hs
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hregB (s : ℝ) (hs : s ∈ Icc 0 B) : deriv beta s ≠ 0 := by
    intro hz
    have hu := hunitB s hs
    simp only [hz, map_zero] at hu
    norm_num at hu
  have orth_independent (p v w : AnnulusCoordinates) (hv : v ≠ 0) (hw : w ≠ 0)
      (ho : N.metric.inner p v w = 0) :
      LinearIndependent ℝ (![v, w] : Fin 2 → AnnulusCoordinates) := by
    rw [linearIndependent_fin2]
    refine ⟨hw, ?_⟩
    intro c he
    change c • w = v at he
    have hpos := N.metric.pos p w hw
    rw [← he, map_smul, smul_apply, smul_eq_mul] at ho
    have hc0 : c = 0 := (mul_eq_zero.mp ho).resolve_right hpos.ne'
    apply hv
    simpa only [hc0, zero_smul] using he.symm
  have hindA := orth_independent (base 0) (deriv base 0) (deriv alpha 0)
    (hreg 0 ⟨le_rfl, hD.le⟩) (hregA 0 ⟨le_rfl, hA.le⟩) horthA
  have hindB := orth_independent (base D) (-deriv base D) (deriv beta 0)
    (neg_ne_zero.mpr (hreg D ⟨hD.le, le_rfl⟩)) (hregB 0 ⟨le_rfl, hB.le⟩)
    (by rw [map_neg, neg_apply, horthB, neg_zero])
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  have hclosure : closure U ∪ closure V = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ frontier U
    · exact Or.inl (frontier_subset_closure hz)
    · have hz' : z ∈ U ∪ V := by rwa [hcover]
      exact hz'.elim (fun h => Or.inl (subset_closure h)) (fun h => Or.inr (subset_closure h))
  have hsmall : max K 0 * intrinsicAnnulusArea N.metric +
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b < Real.pi := by
    have hscaled := mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
    have hlocal := hturn a b hab hperiod hshort
    linarith only [hscaled, hlocal, hbudget, Real.pi_pos]
  obtain ⟨phi, J, hphi, hzero, haxisA, haxisB, hcorner⟩ :=
    m64Intrinsic_small_triangle_terminal_convex_coordinates N hb ha hc hD hA hB hbi hai hci
      hreg hstartA hstartB hmeet hbaseA hbaseB hsides horthA horthB hgeoA hgeoB
      hunitA hunitB hindT hab hcircleInj hcircle hU hV hUV hfront hfV hclosure hpV
      hinwardA hinwardB hsub hK hsmall
  obtain ⟨u, p, c, eta, hu, hp, hcne, he, _, hei, heu, heT, heinside, hegeo,
      hetan, heunit, hereg⟩ :=
    m64Intrinsic_collision_minimizer_smooth_last_contact N.metric hb ha hc hD hA hB hp0
      hbi hai hci hstartA hstartB hmeet hbaseA hbaseB hsides
      (fun s hs => hreg s (Ioo_subset_Icc_self hs))
      (fun s hs => hregA s (Ioo_subset_Icc_self hs))
      (fun s hs => hregB s (Ioo_subset_Icc_self hs))
      (fun s hs => hgeoA s (Ioo_subset_Icc_self hs))
      (fun s hs => hgeoB s (Ioo_subset_Icc_self hs)) hindA hindB
      (hnorm 0 ⟨le_rfl, hD.le⟩) (hnorm D ⟨hD.le, le_rfl⟩) hinwardA hinwardB
      hU hV hUV hfront hfV hcompact hsub hgamma hgi hg0 hgT hconf hlip hmin ⟨t, ht, hcontact⟩
  have heinner (s : ℝ) (hs : s ∈ Icc u T) :
      N.metric.inner (eta s) (deriv eta s) (deriv eta s) = 1 := by
    have hsq : N.metric.tangentNorm (eta s) (deriv eta s) ^ 2 =
        N.metric.inner (eta s) (deriv eta s) (deriv eta s) :=
      Real.sq_sqrt (N.metric.pos (eta s) (deriv eta s) (hereg s hs)).le
    rw [heunit s hs, one_pow] at hsq
    exact hsq.symm
  have hsideA : MapsTo alpha (Icc 0 A) (frontier U) := by
    intro s hs
    rw [hfront]
    exact Or.inr (Or.inl (mem_image_of_mem alpha hs))
  have hsideB : MapsTo beta (Icc 0 B) (frontier U) := by
    intro s hs
    rw [hfront]
    exact Or.inr (Or.inr (mem_image_of_mem beta hs))
  obtain ⟨_, _, heA, heB⟩ := m64Intrinsic_interior_geodesic_arrival_strict_corner
    N.metric ha hc he hA hB hu.2 hgeoA hgeoB hegeo heT (heT.trans hmeet) hU
    hsideA hsideB heinside (hereg T ⟨hu.2.le, le_rfl⟩) J
    (heT.symm ▸ hphi) (heT.symm ▸ hzero) haxisA haxisB
    (heT.symm ▸ hcorner.mono (fun _ hz => hz.mp))
  exact m64Intrinsic_short_circle_last_contact_tail_impossible N hb ha hc he hA hB hp hu.2
    hbi hai hci hei hstartA hstartB hmeet heu heT hbaseA hbaseB hreg hcne hetan
    horthA horthB hgeoA hgeoB hegeo hunitA hunitB heinner
    (LinearIndependent.pair_symm_iff.mpr heA) (LinearIndependent.pair_symm_iff.mpr heB)
    hinwardA hinwardB harcs hU hV hpV hbV hUV hcover hfV hfront heinside hsub
    hK hturn harea hbudget

end PoincareConjecture
