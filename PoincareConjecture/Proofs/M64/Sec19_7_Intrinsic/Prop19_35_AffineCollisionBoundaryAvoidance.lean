import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CollisionBaseAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AffineCircleSubarcs
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCollisionTransverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix ENNReal

namespace PoincareConjecture

theorem m64Intrinsic_affine_collision_minimizer_interior
    (N : IntrinsicAnnulus) {base alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {x d D A B p0 r : ℝ} (hparam : base = fun t => intrinsicAnnulusBoundary 1 (x + d * t))
    (hd : d ≠ 0) (hD : 0 < D) (hA : 0 < A) (hB : 0 < B) (hp0 : p0 ∈ Ioo 0 D)
    (hbi : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hci : InjOn beta (Icc 0 B))
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (horthA : N.metric.inner (base 0) (deriv base 0) (deriv alpha 0) = 0)
    (horthB : N.metric.inner (base D) (deriv base D) (deriv beta 0) = 0)
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (haInterior : ∀ t ∈ Ioc 0 A, 1 < ‖alpha t‖)
    (hbInterior : ∀ t ∈ Ioc 0 B, 1 < ‖beta t‖)
    (hinwardA : 0 < inner ℝ (base 0) (deriv alpha 0))
    (hinwardB : 0 < inner ℝ (base D) (deriv beta 0))
    (hperiod : |d * D| < rampPeriod)
    (hshort : intrinsicBoundaryLength N.metric 1 (min x (x + d * D))
      (max x (x + d * D)) ≤ r)
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
    MapsTo gamma (Ioo 0 T) U := by
  obtain ⟨hbaseSmooth, hderiv, hnorm, hreg⟩ :=
    m64Intrinsic_affine_inner_circle_properties N x d hd
  have hc : ContDiff ℝ ∞ base := by simpa only [hparam] using hbaseSmooth
  have hbaseDeriv (t : ℝ) : deriv base t =
      d • deriv (intrinsicAnnulusBoundary 1) (x + d * t) := by
    simpa only [hparam] using hderiv t
  have hbaseReg (t : ℝ) : deriv base t ≠ 0 := by simpa only [hparam] using hreg t
  have hbaseNorm (t : ℝ) : ‖base t‖ = 1 := by simpa only [hparam] using hnorm t
  have hb0 : base 0 = intrinsicAnnulusBoundary 1 x := by
    simp only [hparam, mul_zero, add_zero]
  have hbD : base D = intrinsicAnnulusBoundary 1 (x + d * D) := congrFun hparam D
  have hcOrthA : N.metric.inner (intrinsicAnnulusBoundary 1 x)
      (deriv (intrinsicAnnulusBoundary 1) x) (deriv alpha 0) = 0 := by
    have h := horthA
    rw [hb0, hbaseDeriv] at h
    simp only [mul_zero, add_zero, map_smul, smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hd
  have hcOrthB : N.metric.inner (intrinsicAnnulusBoundary 1 (x + d * D))
      (deriv (intrinsicAnnulusBoundary 1) (x + d * D)) (deriv beta 0) = 0 := by
    have h := horthB
    rw [hbD, hbaseDeriv] at h
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hd
  have himage : base '' Icc 0 D = intrinsicAnnulusBoundary 1 ''
      Icc (min x (x + d * D)) (max x (x + d * D)) := by
    rw [hparam]
    change (intrinsicAnnulusBoundary 1 ∘ ((fun s => x + s) ∘ fun t => d * t)) '' Icc 0 D = _
    rw [image_comp, ← uIcc_of_le hD.le, image_comp,
      image_const_mul_uIcc, image_const_add_uIcc]
    simp only [mul_zero, add_zero]
    rfl
  have hclosure : closure U ∪ closure V = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ frontier U
    · exact Or.inl (frontier_subset_closure hz)
    · have hz' : z ∈ U ∪ V := by rwa [hcover]
      exact hz'.elim (fun h => Or.inl (subset_closure h)) (fun h => Or.inr (subset_closure h))
  have hindT := m64Intrinsic_short_normal_collision_transverse N ha hb hA hB hai hci
    (hstartA.symm.trans hb0) (hstartB.symm.trans hbD) haInterior hbInterior hgeoA hgeoB
    (hunitA 0 ⟨le_rfl, hA.le⟩) (hunitB 0 ⟨le_rfl, hB.le⟩) hcOrthA hcOrthB
    (hb0 ▸ hinwardA) hmeet hsides
    (by simpa only [add_sub_cancel_left] using hperiod) hU hV hUV
    (by rw [← himage]; exact hfront) hfV hclosure hpV hsub hK hturn harea hbudget hshort
  have harcs : ∀ l ∈ Icc 0 D, ∀ v ∈ Icc 0 D, l ≤ v →
      ∃ a b : ℝ, a ≤ b ∧ b ≤ a + rampPeriod ∧
        InjOn (intrinsicAnnulusBoundary 1) (Icc a b) ∧
        base '' Icc l v = intrinsicAnnulusBoundary 1 '' Icc a b ∧
        intrinsicBoundaryLength N.metric 1 a b ≤ r := by
    intro l hl v hv hlv
    simpa only [hparam] using
      m64Intrinsic_affine_inner_circle_subarc N hD.le hl hv hlv hperiod hshort
  have hbaseAvoid := m64Intrinsic_short_collision_minimizer_avoids_base N hc ha hb
    hD hA hB hp0 hbi hai hci hstartA hstartB hmeet hbaseA hbaseB hsides
    (fun t _ => hbaseReg t) horthA horthB hgeoA hgeoB hunitA hunitB hindT
    hinwardA hinwardB harcs hU hV hpV hbV hUV hcover hfV hfront hsub
    hgamma hgi hg0 hgT hconf hlip hmin hK hturn harea hbudget
  have hregA (t : ℝ) (ht : t ∈ Icc 0 A) : deriv alpha t ≠ 0 := by
    intro hz
    have hu := hunitA t ht
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hregB (t : ℝ) (ht : t ∈ Icc 0 B) : deriv beta t ≠ 0 := by
    intro hz
    have hu := hunitB t ht
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
    (hbaseReg 0) (hregA 0 ⟨le_rfl, hA.le⟩) horthA
  have hindB := orth_independent (base D) (-deriv base D) (deriv beta 0)
    (neg_ne_zero.mpr (hbaseReg D)) (hregB 0 ⟨le_rfl, hB.le⟩)
    (by rw [map_neg, neg_apply, horthB, neg_zero])
  have hcompact : IsCompact (closure U) :=
    m64Intrinsic_standardAnnulus_isCompact.of_isClosed_subset isClosed_closure hsub
  have hsideAvoid := m64Intrinsic_constrained_minimizer_avoids_collision_sides N.metric hc ha hb
    hD hA hB hp0 hbi hai hci hstartA hstartB hmeet hbaseA hbaseB hsides
    (fun t ht => hregA t (Ioo_subset_Icc_self ht))
    (fun t ht => hregB t (Ioo_subset_Icc_self ht))
    (fun t ht => hgeoA t (Ioo_subset_Icc_self ht))
    (fun t ht => hgeoB t (Ioo_subset_Icc_self ht)) hindA hindB (hbaseNorm 0) (hbaseNorm D)
    hinwardA hinwardB hU hV hUV hfront hfV hcompact hsub hgamma hgi hg0 hgT hconf hlip hmin
  intro t ht
  by_contra hn
  have hf : gamma t ∈ frontier U :=
    ⟨hconf (Ioo_subset_Icc_self ht), by simpa only [hU.interior_eq] using hn⟩
  rw [hfront] at hf
  exact hf.elim (hbaseAvoid t ht) (hsideAvoid t ht)

theorem m64Intrinsic_constrained_minimizer_geodesic_of_open_confinement
    (G : RiemannianMetric 2 AnnulusCoordinates) {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hinside : MapsTo gamma (Ioo 0 T) U)
    (hlip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma s → tau 1 = gamma t → MapsTo tau (Icc 0 1) (closure U) →
          ENNReal.ofReal (t - s) ≤ m64IntrinsicCurveVariation G tau 0 1) :
    G.IsGeodesicOn gamma (Ioo 0 T) ∧
      ∀ t ∈ Ioo 0 T, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ gamma t := by
  have hUi : U ⊆ interior (closure U) := by
    calc
      U = interior U := hU.interior_eq.symm
      _ ⊆ interior (closure U) := interior_mono subset_closure
  obtain ⟨hgeo, hsmooth⟩ :=
    m64Intrinsic_constrained_minimizer_interior_geodesic G hcompact hlip hmin
  exact ⟨fun t ht => hgeo t ⟨ht, hUi (hinside ht)⟩,
    fun t ht => hsmooth t ht (hUi (hinside ht))⟩

end PoincareConjecture
