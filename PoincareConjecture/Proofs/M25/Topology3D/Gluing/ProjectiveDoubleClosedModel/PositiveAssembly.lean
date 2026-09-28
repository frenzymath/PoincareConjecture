import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveDoubleClosedModel.CoverTransport
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CapTruncation
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.AntipodalPunctureExpansion
import PoincareConjecture.Proofs.M25.AppA_21_Local.ProjectiveDoubleModel
import PoincareConjecture.Proofs.M25.AppA_21_Local.ClosedComponentPacking
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapCoordinates











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M25.Topology3D

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

private theorem positive_lowerCut_cover
    (C : ClosedModelCapData g)
    (P : PoincareConjecture.StandardPuncturedProjectiveCover M C.puncture C.carrier)
    {s : ℝ} (hs : s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    Nonempty (PoincareConjecture.StandardPuncturedProjectiveCover M C.puncture
      (interior (C.carrier \ C.region s C.epsilon⁻¹))) := by
  let A : TopologicalSpace.Opens M := ⟨C.carrier, C.carrier_open⟩
  let B : TopologicalSpace.Opens M :=
    ⟨interior (C.carrier \ C.region s C.epsilon⁻¹), isOpen_interior⟩
  obtain ⟨_, J, _⟩ := capCertificate_exists_lowerCut_diffeomorph C
    (r := (-C.epsilon⁻¹ + s) / 2) (by linarith [hs.1])
    (by linarith [hs.1]) hs.2
  change Diffeomorph (𝓡 3) (𝓡 3) A B ∞ at J
  obtain ⟨x, hx⟩ := C.carrier_connected.nonempty
  obtain ⟨PA⟩ := standardPuncturedProjectiveCover_nonempty_corestrict_opens
    P A Subset.rfl ⟨x, hx⟩
  obtain ⟨PB⟩ := standardPuncturedProjectiveCover_nonempty_postcompose_diffeomorph PA J
  have hA : (Subtype.val : A → M) ⁻¹' C.carrier = univ :=
    eq_univ_of_forall (fun y => y.property)
  have hJB : (J : A → B) '' ((Subtype.val : A → M) ⁻¹' C.carrier) = univ := by
    rw [hA, image_univ]
    exact range_eq_univ.mpr J.surjective
  rw [hJB] at PB
  refine ⟨{
    cover := Subtype.val ∘ PB.cover
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := ?_ }⟩
  · rw [image_comp, PB.image_eq, image_univ]
    exact Subtype.range_val
  · intro x y hx hy
    change (PB.cover x).val = (PB.cover y).val ↔ x = y ∨ x = -y
    rw [← Subtype.ext_iff]
    exact PB.fibers x y hx hy
  · intro x
    exact (PB.local_diffeomorph x).comp (𝓡 3) M
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) B (PB.cover x))

private theorem positive_double_of_cut_covers
    (C1 C2 : ClosedModelCapData g)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier))
    (hconnected : IsConnected (C1.carrier ∪ C2.carrier))
    {s : ℝ} (hs : s ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹)
    (p2 : RealProjectiveThree)
    (P1 : PoincareConjecture.StandardPuncturedProjectiveCover M C1.puncture
      (interior (C1.carrier \ C1.region s C1.epsilon⁻¹)))
    (P2 : PoincareConjecture.StandardPuncturedProjectiveCover M p2
      ((C1.carrier ∪ C2.carrier) \
        (C1.carrier \ C1.region s C1.epsilon⁻¹))) :
    let U : TopologicalSpace.Opens M :=
      ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
    Nonempty (PoincareConjecture.SmoothProjectiveDoubleModel U) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let N := C1
  let L := C1.epsilon⁻¹
  let U : TopologicalSpace.Opens M :=
    ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
  let K := C1.carrier \ N.region s L
  let V := interior K
  let W := (U : Set M) \ K
  let Sigma := N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ))
  change s ∈ Ioo (-L) L at hs
  have hKclosed : IsClosed K := (C1.isCompact_end_neck_lower_cut hs).isClosed
  have hVeq : V = C1.closed_core ∪ N.region (-L) s :=
    (C1.end_neck_lower_cut_topology hs).2.2.2.1
  have hfront : frontier K = Sigma :=
    (C1.end_neck_lower_cut_topology hs).2.2.2.2.2.1
  have hSigma : Sigma = K \ V := by
    rw [← hfront, frontier, hKclosed.closure_eq]
  have hVsub : V ⊆ (U : Set M) := fun _ hx => Or.inl (interior_subset hx).1
  obtain ⟨y, hy⟩ := hconnected.nonempty
  let y0 : U := ⟨y, hy⟩
  obtain ⟨B1⟩ := standardPuncturedProjectiveCover_nonempty_corestrict_opens
    P1 U hVsub y0
  obtain ⟨B2⟩ := standardPuncturedProjectiveCover_nonempty_corestrict_opens
    P2 U sdiff_subset y0
  let eta := min (s + L) (L - s) / 2
  have hsum : 0 < s + L := by linarith [hs.1]
  have hdiff : 0 < L - s := by linarith [hs.2]
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (lt_min hsum hdiff) (by norm_num)
  have hminus : -L < s - eta := by
    have := min_le_left (s + L) (L - s)
    dsimp [eta]
    linarith [hs.1]
  have hplus : s + eta < L := by
    have := min_le_right (s + L) (L - s)
    dsimp [eta]
    linarith [hs.2]
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-1 : ℝ) 1
  have hOmega : IsOpen Omega := isOpen_univ.prod isOpen_Ioo
  let k0 (z : RoundCylinderSpace) := N.coordinate_map (z.1, s + eta * z.2)
  have hheight {z : RoundCylinderSpace} (hz : z ∈ Omega) :
      s + eta * z.2 ∈ Ioo (-L) L := by
    have hlo := mul_lt_mul_of_pos_left hz.2.1 heta
    have hhi := mul_lt_mul_of_pos_left hz.2.2 heta
    constructor <;> linarith
  have hdom {z : RoundCylinderSpace} (hz : z ∈ Omega) :
      (z.1, s + eta * z.2) ∈ N.cylinderDomain := ⟨mem_univ _, hheight hz⟩
  have hkU {z : RoundCylinderSpace} (hz : z ∈ Omega) : k0 z ∈ (U : Set M) :=
    Or.inl (C1.end_chart_target_subset (N.coordinate_map_mem (hdom hz)))
  let kappa : RoundCylinderSpace → U := fun z =>
    if hz : z ∈ Omega then ⟨k0 z, hkU hz⟩ else y0
  have hkval {z : RoundCylinderSpace} (hz : z ∈ Omega) : (kappa z).val = k0 z := by
    simp only [kappa, dif_pos hz]
  let height : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    { toFun := fun t => s + eta * t
      invFun := fun t => (t - s) / eta
      left_inv := by intro t; field_simp [heta.ne']; ring
      right_inv := by intro t; field_simp [heta.ne']; ring
      contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
      contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const eta).contMDiff }
  let A := (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr height
  have hNsource : N.end_chart.source = N.cylinderDomain := N.end_chart_source
  let n : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace M ∞ :=
    { toPartialEquiv := N.end_chart.toPartialEquiv
      open_source := N.end_chart.open_source
      open_target := N.end_chart.open_target
      contMDiffOn_toFun := N.end_chart_smooth
      contMDiffOn_invFun := N.end_chart_inverse_smooth }
  have hnloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      N.coordinate_map N.cylinderDomain :=
    fun z => ⟨n, hNsource.symm ▸ z.2, fun _ _ => rfl⟩
  have hk0loc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ k0 Omega := by
    intro z
    exact (A.isLocalDiffeomorph z.1).comp (𝓡 3) M (hnloc ⟨A z.1, hdom z.2⟩)
  have hkloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ kappa Omega := by
    intro z
    have hk := hk0loc z
    have hi := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U (kappa z)
    have hinv : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hi.localInverse (k0 z) := by
      rw [← hkval z.2]
      exact hi.localInverse_isLocalDiffeomorphAt
    apply (hk.comp (𝓡 3) U hinv).congr_of_eventuallyEq
    have hxsource : k0 z ∈ hi.localInverse.source := by
      rw [← hkval z.2]
      exact hi.localInverse_mem_source
    have hev : ∀ᶠ w in 𝓝 (z : RoundCylinderSpace), k0 w ∈ hi.localInverse.source :=
      hk.contMDiffAt.continuousAt (hi.localInverse_open_source.mem_nhds hxsource)
    filter_upwards [hev, hOmega.mem_nhds z.2] with w hw hwO
    apply Subtype.ext
    rw [hkval hwO]
    exact (hi.localInverse_right_inv hw).symm
  have hkinj : InjOn kappa Omega := by
    intro z hz w hw heq
    have heq' := congrArg Subtype.val heq
    rw [hkval hz, hkval hw] at heq'
    exact A.injective (N.end_chart.injOn
      (hNsource.symm ▸ hdom hz) (hNsource.symm ▸ hdom hw) heq')
  have hkopen : IsOpen (kappa '' Omega) := by
    have hl : IsLocalHomeomorph (fun z : Omega => kappa z.val) := by
      apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      exact hkloc.isLocalHomeomorphOn.comp
        hOmega.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun z _ => z.property)
    have heq : (fun z : Omega => kappa z.val) '' univ = kappa '' Omega := by
      ext x
      constructor
      · rintro ⟨z, _, rfl⟩
        exact ⟨z.val, z.property, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, mem_univ _, rfl⟩
    rw [← heq]
    exact hl.isOpenMap _ isOpen_univ
  have hkzero (q : UnitTwoSphere) : (kappa (q, 0)).val = N.coordinate_map (q, s) := by
    rw [hkval (show (q, 0) ∈ Omega from ⟨mem_univ _, by norm_num, by norm_num⟩)]
    simp only [k0, mul_zero, add_zero]
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconnected
  refine ⟨{
    compact := isCompact_univ
    connected := isConnected_univ
    sphere := (Subtype.val : U → M) ⁻¹' Sigma
    first_region := (Subtype.val : U → M) ⁻¹' V
    second_region := (Subtype.val : U → M) ⁻¹' W
    first_open := isOpen_interior.preimage continuous_subtype_val
    second_open := (U.isOpen.sdiff hKclosed).preimage continuous_subtype_val
    disjoint := ?_
    sphere_disjoint := ?_
    cover := ?_
    first_puncture := C1.puncture
    second_puncture := p2
    first_model := B1
    second_model := B2
    collar := kappa
    collar_local_diffeomorph := hkloc
    collar_injective := hkinj
    collar_open := hkopen
    collar_sphere := ?_
    collar_negative := ?_
    collar_positive := ?_ }⟩
  · exact disjoint_left.mpr (fun _ hx hy => hy.2 (interior_subset hx))
  · apply disjoint_left.mpr
    intro x hx hy
    change x.val ∈ Sigma at hx
    rw [hSigma] at hx
    exact hy.elim hx.2 (fun h => h.2 hx.1)
  · apply eq_univ_of_forall
    intro x
    by_cases hxV : x.val ∈ V
    · exact Or.inl (Or.inl hxV)
    · by_cases hxK : x.val ∈ K
      · exact Or.inr (hSigma.symm ▸ ⟨hxK, hxV⟩)
      · exact Or.inl (Or.inr ⟨x.property, hxK⟩)
  · apply Subset.antisymm
    · rintro _ ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      change (kappa (q, 0)).val ∈ Sigma
      rw [hkzero]
      exact ⟨(q, s), ⟨mem_univ _, rfl⟩, rfl⟩
    · intro x hx
      obtain ⟨⟨q, t⟩, ⟨_, ht⟩, htx⟩ := hx
      have hts : t = s := ht
      subst t
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, Subtype.ext ((hkzero q).trans htx)⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzO : z ∈ Omega := ⟨mem_univ _, hz.2.1, hz.2.2.trans (by norm_num)⟩
    change (kappa z).val ∈ V
    rw [hkval hzO, hVeq]
    refine Or.inr ⟨N.coordinate_map_mem (hdom hzO), ?_⟩
    rw [N.coordinate_inverse_coordinate_map (hdom hzO)]
    exact ⟨(hheight hzO).1, by nlinarith [mul_neg_of_pos_of_neg heta hz.2.2]⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzO : z ∈ Omega := ⟨mem_univ _, (by norm_num : (-1 : ℝ) < 0).trans hz.2.1,
      hz.2.2⟩
    change (kappa z).val ∈ W
    refine ⟨(kappa z).property, ?_⟩
    rw [hkval hzO]
    intro hxK
    apply hxK.2
    refine ⟨N.coordinate_map_mem (hdom hzO), ?_⟩
    rw [N.coordinate_inverse_coordinate_map (hdom hzO)]
    exact ⟨by nlinarith [mul_pos heta hz.2.1], (hheight hzO).2⟩




theorem capCertificates_nonempty_projective_double_of_positive_compact_side
    (C1 C2 : ClosedModelCapData g)
    (P1 : PoincareConjecture.StandardPuncturedProjectiveCover M C1.puncture C1.carrier)
    (P2 : PoincareConjecture.StandardPuncturedProjectiveCover M C2.puncture C2.carrier)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier))
    (v c h : ℝ) (hv : v ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹)
    (hh : 0 < h) (hleft : v < c - h) (hright : c + h < C1.epsilon⁻¹)
    (hcuts : ∀ a b : ℝ, v < a → a < b → b < C1.epsilon⁻¹ →
      ((C1.carrier ∪ C2.carrier) \
        interior (C1.carrier \ C1.region a C1.epsilon⁻¹)) ⊆
          C2.carrier ∧
      C1.coordinate_map '' (univ ×ˢ Icc a b) ⊆ C2.carrier)
    {psi : UnitTwoSphere × ℝ → E3} (S : SchoenfliesData psi (1 / 4))
    (e : OpenPartialHomeomorph E3 UnitThreeSphere)
    (hes : e.source = ball 0 (S.radial (7 / 8)))
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hdis : Disjoint e.target ((fun x : UnitThreeSphere => -x) '' e.target))
    (hpositive :
      projectiveCoverDomain C2.puncture ∩ P2.cover ⁻¹'
        ((C1.carrier ∪ C2.carrier) \
          (C1.carrier \ C1.region (c + h / 2) C1.epsilon⁻¹)) =
        (e '' closedBall 0 (S.radial (1 / 2)) ∪
          (fun x : UnitThreeSphere => -x) ''
            (e '' closedBall 0 (S.radial (1 / 2))))ᶜ) :
    Nonempty (ClosedComponentCertificate .realProjectiveThreeConnectedSum
      (C1.carrier ∪ C2.carrier)) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := C1.epsilon⁻¹
  let s := c + h / 2
  have hvs : v < s := by dsimp [s]; linarith
  have hsL : s < L := by dsimp [s, L]; linarith
  have hs : s ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹ := ⟨hv.1.trans hvs, hsL⟩
  obtain ⟨hQ, hslab⟩ := hcuts s ((s + L) / 2) hvs
    (by linarith) (by linarith)
  let W := (C1.carrier ∪ C2.carrier) \ (C1.carrier \ C1.region s L)
  have hW : W ⊆ C2.carrier := fun _ hx =>
    hQ ⟨hx.1, fun hxi => hx.2 (interior_subset hxi)⟩
  have hmeet : (C1.carrier ∩ C2.carrier).Nonempty := by
    let q := (C1.coordinate_inverse C1.endCenter).1
    have hz : (q, s) ∈ C1.cylinderDomain := ⟨mem_univ _, hs⟩
    exact ⟨C1.coordinate_map (q, s),
      C1.end_chart_target_subset (C1.coordinate_map_mem hz),
      hslab ⟨(q, s), ⟨mem_univ _, le_rfl, by linarith⟩, rfl⟩⟩
  have hconnected := C1.carrier_connected.union hmeet
    C2.carrier_connected
  have hr : 0 < S.radial (1 / 2) := S.radial_pos _ (by constructor <;> norm_num)
  have hrR : S.radial (1 / 2) < S.radial (7 / 8) :=
    S.radial_strictMono (by constructor <;> norm_num)
      (by constructor <;> norm_num) (by norm_num)
  obtain ⟨_, H, _, _, _, _, _, _, _, hHs, hHt, hH, hHi, _, hodd, _⟩ :=
    exists_antipodal_ball_exterior_chart e hr hrR hes he hei hdis
  let p2 : RealProjectiveThree := Quotient.mk' (e 0)
  have hsource : H.source = projectiveCoverDomain p2 :=
    hHs.trans (projectiveCoverDomain_eq_compl_pair (e 0) rfl).symm
  have htarget : H.target = projectiveCoverDomain C2.puncture ∩ P2.cover ⁻¹' W :=
    hHt.trans hpositive.symm
  obtain ⟨Q2⟩ := exists_puncturedProjective_cover_of_odd_partialHomeomorph
    P2 H hsource htarget hW hH hHi hodd
  obtain ⟨Q1⟩ := positive_lowerCut_cover C1 P1 hs
  obtain ⟨D⟩ := positive_double_of_cut_covers C1 C2 hcompact hconnected hs p2 Q1 Q2
  obtain ⟨T, _⟩ := D.exists_connected_sum_model
  exact ClosedComponentCertificate.nonempty_of_compact_connected_opens
    .realProjectiveThreeConnectedSum
    ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
    hcompact hconnected T ⟨D⟩

end PoincareConjecture.M25.Topology3D
