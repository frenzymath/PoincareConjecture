import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCapCover
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCollarStereographic
import PoincareConjecture.Proofs.M25.Mathlib.CompactBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapCoordinates

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D

theorem capCertificate_exists_projective_filled_end_lift
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g)
    (P : PoincareConjecture.StandardPuncturedProjectiveCover
      M C.puncture C.carrier) :
    let H := C.epsilon⁻¹
    let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-H) H
    ∃ (p0 : UnitThreeSphere) (F : RoundCylinderSpace → UnitThreeSphere),
      (Quotient.mk' p0 : RealProjectiveThree) = C.puncture ∧
      MapsTo F Omega (projectiveCoverDomain C.puncture) ∧
      EqOn (P.cover ∘ F) C.coordinate_map Omega ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ F Omega ∧
      InjOn F Omega ∧
      Disjoint (F '' Omega) ((fun z => -F z) '' Omega) ∧
      ∀ s ∈ Ioo (-H) H,
        let T : Set UnitThreeSphere := F '' (univ ×ˢ Ioo s H)
        let Sigma : Set UnitThreeSphere := F '' (univ ×ˢ ({s} : Set ℝ))
        let B : Set UnitThreeSphere := T ∪ {p0}
        IsOpen B ∧ IsConnected B ∧ IsCompact (closure B) ∧
        closure B = B ∪ Sigma ∧ interior (closure B) = B ∧
        frontier (closure B) = Sigma ∧
        Disjoint (closure B)
          ((fun x : UnitThreeSphere => -x) '' closure B) ∧
        projectiveCoverDomain C.puncture ∩
            P.cover ⁻¹' (C.carrier \ C.region s H) =
          (B ∪ (fun x : UnitThreeSphere => -x) '' B)ᶜ := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let N := C
  let H := C.epsilon⁻¹
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-H) H
  let D := projectiveCoverDomain C.puncture
  have hH : 0 < H := inv_pos.mpr C.epsilon_pos
  have hzero : (0 : ℝ) ∈ Ioo (-H) H := ⟨neg_lt_zero.mpr hH, hH⟩
  have hOmega : Omega = N.cylinderDomain := rfl
  have hNsource : N.end_chart.source = N.cylinderDomain := N.end_chart_source
  have hOmegaOpen : IsOpen Omega := isOpen_univ.prod isOpen_Ioo
  let n : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace M ∞ :=
    { toPartialEquiv := N.end_chart.toPartialEquiv
      open_source := N.end_chart.open_source
      open_target := N.end_chart.open_target
      contMDiffOn_toFun := N.end_chart_smooth
      contMDiffOn_invFun := N.end_chart_inverse_smooth }
  have hnloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      N.coordinate_map Omega := by
    intro z
    refine ⟨n, ?_, fun _ _ => rfl⟩
    change z.val ∈ N.end_chart.source
    rw [hNsource, ← hOmega]
    exact z.property
  have hninj : InjOn N.coordinate_map Omega := by
    rw [hOmega, ← hNsource]
    exact N.end_chart.injOn
  have hncap : MapsTo N.coordinate_map Omega C.carrier :=
    fun _ hz => C.end_chart_target_subset (N.coordinate_map_mem (hOmega ▸ hz))
  let q0 := (N.coordinate_inverse N.endCenter).1
  have hbasecap : N.coordinate_map (q0, 0) ∈ C.carrier :=
    hncap (show (q0, 0) ∈ Omega from ⟨mem_univ _, hzero⟩)
  obtain ⟨x0, hx0, hx0map⟩ := P.image_eq.symm.subset hbasecap
  obtain ⟨F, _, hFD, hFc, hFloc, hFinj, _, _, _, _, hFdis, _⟩ :=
    StandardPuncturedProjectiveCover.exists_based_projective_collar_lift P
      N.coordinate_map hzero hnloc hninj hncap q0 x0 hx0 hx0map
  have hcover {z : RoundCylinderSpace} (hz : z ∈ Omega) :
      P.cover (F z) = N.coordinate_map z := hFc hz
  let negE : UnitThreeSphere ≃ₜ UnitThreeSphere :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := neg_neg
      right_inv := neg_neg
      continuous_toFun := continuous_neg
      continuous_invFun := continuous_neg }
  have hnegmem (A : Set UnitThreeSphere) (x : UnitThreeSphere) :
      x ∈ negE '' A ↔ -x ∈ A := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      change -y = x at hxy
      simpa only [← hxy, neg_neg] using hy
    · intro hx
      exact ⟨-x, hx, neg_neg x⟩
  have hFdis' : Disjoint (F '' Omega) (negE '' (F '' Omega)) := by
    rw [disjoint_left] at hFdis ⊢
    rintro x hx ⟨y, ⟨z, hz, rfl⟩, heq⟩
    exact hFdis hx ⟨z, hz, heq⟩
  have hFDimage : F '' Omega ⊆ D := image_subset_iff.mpr hFD
  have hopenImage (A : Set RoundCylinderSpace) (hA : IsOpen A) (hAO : A ⊆ Omega) :
      IsOpen (F '' A) := by
    have hlocal : IsLocalHomeomorph (fun z : Omega => F z.val) := by
      apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      exact hFloc.isLocalHomeomorphOn.comp
        hOmegaOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun z _ => z.property)
    have heq : (fun z : Omega => F z.val) '' (Subtype.val ⁻¹' A) = F '' A := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.val, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hAO hz⟩, hz, rfl⟩
    rw [← heq]
    exact hlocal.isOpenMap _ (hA.preimage continuous_subtype_val)
  have hFopen := hopenImage Omega hOmegaOpen Subset.rfl
  have hnegOpen := negE.isOpenMap _ hFopen
  have hnotOppClosure {x : UnitThreeSphere} (hx : x ∈ negE '' (F '' Omega)) :
      x ∉ closure (F '' Omega) := by
    intro hc
    obtain ⟨y, hyneg, hyF⟩ := mem_closure_iff.mp hc _ hnegOpen hx
    exact disjoint_left.mp hFdis' hyF hyneg
  let T (s : ℝ) := F '' (univ ×ˢ Ioo s H)
  let Sigma (s : ℝ) := F '' (univ ×ˢ ({s} : Set ℝ))
  let K (s : ℝ) := C.carrier \ N.region s H
  let Ktilde (s : ℝ) := D ∩ P.cover ⁻¹' K s
  have htailSub {s : ℝ} (hs : -H < s) : univ ×ˢ Ioo s H ⊆ Omega :=
    fun _ hz => ⟨mem_univ _, hs.trans hz.2.1, hz.2.2⟩
  have hTsub {s : ℝ} (hs : -H < s) : T s ⊆ F '' Omega := image_mono (htailSub hs)
  have hSigmaSub {s : ℝ} (hs : s ∈ Ioo (-H) H) : Sigma s ⊆ F '' Omega := by
    apply image_mono
    rintro ⟨q, r⟩ ⟨_, hr⟩
    have hr' : r = s := hr
    subst r
    exact ⟨mem_univ _, hs⟩
  have hTopen {s : ℝ} (hs : -H < s) : IsOpen (T s) :=
    hopenImage _ (isOpen_univ.prod isOpen_Ioo) (htailSub hs)
  have hTconnected {s : ℝ} (hs : s ∈ Ioo (-H) H) : IsConnected (T s) :=
    (isConnected_univ.prod (isConnected_Ioo hs.2)).image F
      (hFloc.contMDiffOn.continuousOn.mono (htailSub hs.1))
  have hTanti {s t : ℝ} (hst : s ≤ t) : T t ⊆ T s := by
    apply image_mono
    exact fun _ hz => ⟨mem_univ _, hst.trans_lt hz.2.1, hz.2.2⟩
  have hTdis {s : ℝ} (hs : -H < s) : Disjoint (T s) (negE '' T s) :=
    hFdis'.mono (hTsub hs) (image_mono (hTsub hs))
  have hregionImage {s : ℝ} (hs : s ∈ Ioo (-H) H) :
      N.coordinate_map '' (univ ×ˢ Ioo s H) = N.region s H := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hzo := hOmega ▸ htailSub hs.1 hz
      exact ⟨N.coordinate_map_mem hzo, by
        simpa only [N.coordinate_inverse_coordinate_map hzo, mem_Ioo] using hz.2⟩
    · intro x hx
      exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩,
        N.coordinate_map_coordinate_inverse hx.1⟩
  have hpairTail {s : ℝ} (hs : s ∈ Ioo (-H) H) :
      D ∩ P.cover ⁻¹' N.region s H = T s ∪ negE '' T s := by
    ext x
    constructor
    · rintro ⟨hxD, hx⟩
      obtain ⟨z, hz, hzx⟩ := (hregionImage hs).symm ▸ hx
      have hzo := htailSub hs.1 hz
      have hc : P.cover x = P.cover (F z) := hzx.symm.trans (hFc hzo).symm
      rcases (P.fibers x (F z) hxD (hFD hzo)).mp hc with h | h
      · exact Or.inl ⟨z, hz, h.symm⟩
      · exact Or.inr ⟨F z, ⟨z, hz, rfl⟩, h.symm⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨y, ⟨z, hz, rfl⟩, rfl⟩)
      · refine ⟨hFD (htailSub hs.1 hz), ?_⟩
        change P.cover (F z) ∈ N.region s H
        rw [hcover (htailSub hs.1 hz)]
        exact (hregionImage hs).subset ⟨z, hz, rfl⟩
      · refine ⟨(neg_mem_projectiveCoverDomain_iff _ _).mpr (hFD (htailSub hs.1 hz)), ?_⟩
        change P.cover (-F z) ∈ N.region s H
        rw [StandardPuncturedProjectiveCover.cover_neg P (hFD (htailSub hs.1 hz)),
          hcover (htailSub hs.1 hz)]
        exact (hregionImage hs).subset ⟨z, hz, rfl⟩
  have hKcompact {s : ℝ} (hs : s ∈ Ioo (-H) H) : IsCompact (Ktilde s) := by
    have hK := C.isCompact_end_neck_lower_cut hs
    have hsub : K s ⊆ range (Subtype.val : C.carrier → M) := by
      rw [Subtype.range_coe]
      exact sdiff_subset
    have hKs : IsCompact ((Subtype.val : C.carrier → M) ⁻¹' K s) :=
      IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hsub
    have hc :=
      (StandardPuncturedProjectiveCover.restrictedCover_isProperMap P).isCompact_preimage hKs
    have heq : Subtype.val '' (StandardPuncturedProjectiveCover.restrictedCover P ⁻¹'
        ((Subtype.val : C.carrier → M) ⁻¹' K s)) = Ktilde s := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.property, hz⟩
      · rintro ⟨hxD, hxK⟩
        exact ⟨⟨x, hxD⟩, hxK, rfl⟩
    rw [← heq]
    exact hc.image continuous_subtype_val
  have hpartition {s : ℝ} (hs : s ∈ Ioo (-H) H) {x : UnitThreeSphere}
      (hxD : x ∈ D) (hxK : x ∉ Ktilde s) : x ∈ T s ∪ negE '' T s := by
    apply (hpairTail hs).subset
    refine ⟨hxD, ?_⟩
    by_contra hx
    exact hxK ⟨hxD, StandardPuncturedProjectiveCover.cover_mem P hxD, hx⟩

  have hpunctured (p : UnitThreeSphere) (W : Set UnitThreeSphere)
      (hW : IsOpen W) (hpW : p ∈ W) :
      ∃ A : Set UnitThreeSphere, IsOpen A ∧ p ∈ A ∧ A ⊆ W ∧ -p ∉ A ∧
        IsConnected (A \ {p}) ∧ p ∈ closure (A \ {p}) := by
    let e := threeSphereStereographic (-p)
    have htarget : e.target = univ := threeSphereStereographic_target (-p)
    have hecont : Continuous e.symm := by
      apply continuousOn_univ.mp
      simpa only [htarget] using e.continuousOn_symm
    have hezero : e.symm 0 = p := by
      simpa only [neg_neg] using threeSphereStereographic_symm_zero (-p)
    have hinj : Function.Injective e.symm := by
      intro x y hxy
      exact e.symm.injOn
        (by change x ∈ e.target; rw [htarget]; trivial)
        (by change y ∈ e.target; rw [htarget]; trivial) hxy
    have h0W : (0 : E3) ∈ e.symm ⁻¹' W := by
      change e.symm 0 ∈ W
      rw [hezero]
      exact hpW
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp (hW.preimage hecont) 0 h0W
    let A := e.symm '' Metric.ball (0 : E3) r
    let Q : Set E3 := {x | 0 < ‖x‖ ∧ ‖x‖ < r}
    have hQ : IsConnected Q :=
      (isPathConnected_norm_annulus (by rw [← Module.finrank_eq_rank]; norm_num)
        (show (0 : ℝ) ≤ 0 from le_rfl) hr).isConnected
    have hAopen : IsOpen A := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
      (by rw [e.symm_source, htarget]; exact subset_univ _)
    have hpA : p ∈ A := ⟨0, Metric.mem_ball_self hr, hezero⟩
    have hAW : A ⊆ W := by
      rintro _ ⟨x, hx, rfl⟩
      exact hrW hx
    have hnegA : -p ∉ A := by
      rintro ⟨x, hx, heq⟩
      have hm := e.map_target (htarget.symm ▸ mem_univ x)
      rw [show e.source = {-p}ᶜ from threeSphereStereographic_source (-p), heq] at hm
      exact hm (mem_singleton _)
    have hpunct : A \ {p} = e.symm '' Q := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hyp⟩
        refine ⟨y, ⟨?_, by simpa only [Metric.mem_ball, dist_zero_right] using hy⟩, rfl⟩
        apply norm_pos_iff.mpr
        intro hy0
        exact hyp (by simp only [hy0, hezero, mem_singleton_iff])
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨y, by simpa only [Metric.mem_ball, dist_zero_right] using hy.2, rfl⟩, ?_⟩
        intro hep
        have hy0 := hinj ((mem_singleton_iff.mp hep).trans hezero.symm)
        exact hy.1.ne' (by rw [hy0, norm_zero])
    have h0Q : (0 : E3) ∈ closure Q := by
      have hc : Continuous (fun t : ℝ => t • (q0 : E3)) := continuous_id.smul continuous_const
      have ht : (0 : ℝ) ∈ closure (Ioo 0 r) := by
        rw [closure_Ioo hr.ne]
        exact ⟨le_rfl, hr.le⟩
      have him : (fun t : ℝ => t • (q0 : E3)) '' Ioo 0 r ⊆ Q := by
        rintro _ ⟨t, ht, rfl⟩
        change 0 < ‖t • (q0 : E3)‖ ∧ ‖t • (q0 : E3)‖ < r
        rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp q0.property,
          mul_one, abs_of_pos ht.1]
        exact ht
      simpa only [zero_smul] using
        closure_mono him (hc.continuousAt.continuousWithinAt.mem_closure_image ht)
    refine ⟨A, hAopen, hpA, hAW, hnegA, ?_, ?_⟩
    · rw [hpunct]
      exact hQ.image e.symm hecont.continuousOn
    · rw [hpunct, ← hezero]
      exact hecont.continuousAt.continuousWithinAt.mem_closure_image h0Q
  obtain ⟨r0, hr0⟩ := Quotient.mk'_surjective C.puncture
  have hr0D : r0 ∉ D := fun h => h hr0
  obtain ⟨A0, hA0, hr0A, hA0K, hnegA0, hA0c, _⟩ :=
    hpunctured r0 (Ktilde 0)ᶜ (hKcompact hzero).isClosed.isOpen_compl
      (fun h => hr0D h.1)
  have hA0partition : A0 \ {r0} ⊆ T 0 ∪ negE '' T 0 := by
    intro x hx
    apply hpartition hzero _ (hA0K hx.1)
    rw [show D = ({r0, -r0} : Set UnitThreeSphere)ᶜ from
      projectiveCoverDomain_eq_compl_pair r0 hr0]
    intro hp
    rcases hp with hp | hp
    · exact hx.2 hp
    · exact hnegA0 (mem_singleton_iff.mp hp ▸ hx.1)
  have hbase : ∃ p0 : UnitThreeSphere, Quotient.mk' p0 = C.puncture ∧
      ∃ A : Set UnitThreeSphere, IsOpen A ∧ p0 ∈ A ∧ A \ {p0} ⊆ T 0 := by
    rcases hA0c.isPreconnected.subset_or_subset (hTopen hzero.1)
      (negE.isOpenMap _ (hTopen hzero.1)) (hTdis hzero.1) hA0partition with h | h
    · exact ⟨r0, hr0, A0, hA0, hr0A, h⟩
    · refine ⟨-r0, (projectiveQuotient_neg r0).trans hr0,
        negE '' A0, negE.isOpenMap _ hA0, ⟨r0, hr0A, rfl⟩, ?_⟩
      rintro x ⟨⟨y, hy, rfl⟩, hne⟩
      have hyr : y ≠ r0 := by
        intro heq
        exact hne (by simp only [heq, mem_singleton_iff]; rfl)
      exact (hnegmem (T 0) y).mp (h ⟨hy, hyr⟩)
  obtain ⟨p0, hp0, A0, hA0open, hp0A0, hA0T⟩ := hbase
  have hp0D : p0 ∉ D := fun h => h hp0
  have hnegp0D : -p0 ∉ D :=
    fun h => hp0D ((neg_mem_projectiveCoverDomain_iff _ _).mp h)
  have hpairD : D = ({p0, -p0} : Set UnitThreeSphere)ᶜ :=
    projectiveCoverDomain_eq_compl_pair p0 hp0
  have haugDis : Disjoint (F '' Omega ∪ {p0}) (negE '' (F '' Omega ∪ {p0})) := by
    rw [disjoint_left]
    rintro x (hx | hx) ⟨y, hy | hy, heq⟩
    · exact disjoint_left.mp hFdis' hx ⟨y, hy, heq⟩
    · subst y
      change -p0 = x at heq
      exact hnegp0D (heq.symm ▸ hFDimage hx)
    · subst x
      change -y = p0 at heq
      have hy' : y = -p0 := by simpa only [neg_neg] using congrArg Neg.neg heq
      exact hnegp0D (hy' ▸ hFDimage hy)
    · subst x
      subst y
      exact ne_neg_of_mem_unit_sphere ℝ p0 heq.symm
  have hfilled {s : ℝ} (hs : s ∈ Ioo (-H) H) :
      IsOpen (T s ∪ {p0}) ∧ p0 ∈ closure (T s) := by
    obtain ⟨A, hA, hpA, hAW, hnegA, hAc, hpcl⟩ :=
      hpunctured p0 (A0 ∩ (Ktilde s)ᶜ)
        (hA0open.inter (hKcompact hs).isClosed.isOpen_compl)
        ⟨hp0A0, fun h => hp0D h.1⟩
    have hAT : A \ {p0} ⊆ T s := by
      by_cases hs0 : s ≤ 0
      · exact fun x hx => hTanti hs0 (hA0T ⟨(hAW hx.1).1, hx.2⟩)
      · have hpart : A \ {p0} ⊆ T s ∪ negE '' T s := by
          intro x hx
          apply hpartition hs _ (hAW hx.1).2
          rw [hpairD]
          intro hp
          rcases hp with hp | hp
          · exact hx.2 hp
          · exact hnegA (mem_singleton_iff.mp hp ▸ hx.1)
        rcases hAc.isPreconnected.subset_or_subset (hTopen hs.1)
          (negE.isOpenMap _ (hTopen hs.1)) (hTdis hs.1) hpart with h | h
        · exact h
        · obtain ⟨x, hx⟩ := hAc.nonempty
          have hxT := hA0T ⟨(hAW hx.1).1, hx.2⟩
          have hxN := image_mono (hTanti (le_of_not_ge hs0)) (h hx)
          exact False.elim (disjoint_left.mp (hTdis hzero.1) hxT hxN)
    have heq : T s ∪ {p0} = T s ∪ A := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact Or.inl hx
        · exact Or.inr ((mem_singleton_iff.mp hx).symm ▸ hpA)
      · rintro (hx | hx)
        · exact Or.inl hx
        · by_cases hxp : x = p0
          · exact Or.inr hxp
          · exact Or.inl (hAT ⟨hx, hxp⟩)
    exact ⟨heq.symm ▸ (hTopen hs.1).union hA, closure_mono hAT hpcl⟩
  have hSigmaClosure {s : ℝ} (hs : s ∈ Ioo (-H) H) : Sigma s ⊆ closure (T s) := by
    rintro _ ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    have ht' : t = s := ht
    subst t
    have hcl : (q, s) ∈ closure (univ ×ˢ Ioo s H) := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hs.2.ne]
      exact ⟨mem_univ _, le_rfl, hs.2.le⟩
    have hcont := (hFloc ⟨(q, s), mem_univ _, hs⟩).contMDiffAt.continuousAt
    exact hcont.continuousWithinAt.mem_closure_image hcl
  have hvalidClosure {s : ℝ} (hs : s ∈ Ioo (-H) H) {x : UnitThreeSphere}
      (hxD : x ∈ D) (hxcl : x ∈ closure (T s)) : x ∈ T s ∪ Sigma s := by
    have hcont := (P.local_diffeomorph ⟨x, hxD⟩).contMDiffAt.continuousAt
    have hxcover : P.cover x ∈ closure (P.cover '' T s) :=
      hcont.continuousWithinAt.mem_closure_image hxcl
    have hnoInt : P.cover x ∉ interior (K s) := by
      apply closure_minimal (t := (interior (K s))ᶜ) _ isOpen_interior.isClosed_compl hxcover
      rintro _ ⟨y, hy, rfl⟩ hi
      have hreg := ((hpairTail hs).symm.subset (Or.inl hy)).2
      exact (interior_subset hi).2 hreg
    by_cases htail : P.cover x ∈ N.region s H
    · rcases (hpairTail hs).subset ⟨hxD, htail⟩ with h | h
      · exact Or.inl h
      · exact False.elim (hnotOppClosure (image_mono (hTsub hs.1) h)
          (closure_mono (hTsub hs.1) hxcl))
    · have hcut : P.cover x ∈ K s :=
        ⟨StandardPuncturedProjectiveCover.cover_mem P hxD, htail⟩
      obtain ⟨_, _, _, _, _, hfront, _⟩ := C.end_neck_lower_cut_topology hs
      have hslice : P.cover x ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) := by
        rw [← hfront, frontier, (C.isCompact_end_neck_lower_cut hs).isClosed.closure_eq]
        exact ⟨hcut, hnoInt⟩
      obtain ⟨z, hz, hzx⟩ := hslice
      have hzo : z ∈ Omega := by
        exact ⟨mem_univ _, (mem_singleton_iff.mp hz.2).symm ▸ hs⟩
      have hc : P.cover x = P.cover (F z) := hzx.symm.trans (hFc hzo).symm
      rcases (P.fibers x (F z) hxD (hFD hzo)).mp hc with h | h
      · exact Or.inr ⟨z, hz, h.symm⟩
      · exact False.elim (hnotOppClosure ⟨F z, ⟨z, hzo, rfl⟩, h.symm⟩
          (closure_mono (hTsub hs.1) hxcl))
  refine ⟨p0, F, hp0, hFD, hFc, hFloc, hFinj, hFdis, ?_⟩
  intro s hs
  change IsOpen (T s ∪ {p0}) ∧ IsConnected (T s ∪ {p0}) ∧
    IsCompact (closure (T s ∪ {p0})) ∧
    closure (T s ∪ {p0}) = (T s ∪ {p0}) ∪ Sigma s ∧
    interior (closure (T s ∪ {p0})) = T s ∪ {p0} ∧
    frontier (closure (T s ∪ {p0})) = Sigma s ∧
    Disjoint (closure (T s ∪ {p0})) (negE '' closure (T s ∪ {p0})) ∧
    Ktilde s = ((T s ∪ {p0}) ∪ negE '' (T s ∪ {p0}))ᶜ
  let B := T s ∪ {p0}
  obtain ⟨hBopen, hpcl⟩ := hfilled hs
  have hBsub : B ⊆ F '' Omega ∪ {p0} := union_subset_union (hTsub hs.1) Subset.rfl
  have hBdis : Disjoint B (negE '' B) := haugDis.mono hBsub (image_mono hBsub)
  have hnegNotClosure {x : UnitThreeSphere} (hx : x ∈ negE '' B) : x ∉ closure B := by
    intro hcl
    obtain ⟨y, hyneg, hyB⟩ := mem_closure_iff.mp hcl _ (negE.isOpenMap _ hBopen) hx
    exact disjoint_left.mp hBdis hyB hyneg
  have hclosure : closure B = B ∪ Sigma s := by
    apply Subset.antisymm
    · intro x hx
      rw [show closure B = closure (T s) ∪ {p0} by
        simp only [B, closure_union, isClosed_singleton.closure_eq]] at hx
      rcases hx with hx | hx
      · by_cases hxD : x ∈ D
        · exact (hvalidClosure hs hxD hx).elim (fun h => Or.inl (Or.inl h)) Or.inr
        · have hp : x ∈ ({p0, -p0} : Set UnitThreeSphere) := by
            simpa only [hpairD, mem_compl_iff, not_not] using hxD
          rcases hp with hp | hp
          · exact Or.inl (Or.inr hp)
          · have hxneg : x ∈ negE '' B :=
              ⟨p0, Or.inr rfl, (mem_singleton_iff.mp hp).symm⟩
            exact False.elim (hnegNotClosure hxneg (closure_mono subset_union_left hx))
      · exact Or.inl (Or.inr hx)
    · rintro _ (hx | hx)
      · exact subset_closure hx
      · exact closure_mono subset_union_left (hSigmaClosure hs hx)
  have hSigmaNotInterior : Sigma s ⊆ (interior (closure B))ᶜ := by
    intro x hx
    change x ∈ F '' (univ ×ˢ ({s} : Set ℝ)) at hx
    obtain ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ := hx
    have ht' : t = s := ht
    subst t
    have hbelow : F '' (univ ×ˢ Ioo (-H) s) ⊆ (closure B)ᶜ := by
      rintro _ ⟨z, hz, rfl⟩ hcl
      have hzo : z ∈ Omega := ⟨mem_univ _, hz.2.1, hz.2.2.trans hs.2⟩
      rw [hclosure] at hcl
      rcases hcl with (⟨w, hw, heq⟩ | hp) | ⟨w, hw, heq⟩
      · have hzw := hFinj (htailSub hs.1 hw) hzo heq
        have hh := congrArg Prod.snd hzw
        exact (not_lt_of_gt hz.2.2) (hh ▸ hw.2.1)
      · exact hp0D (mem_singleton_iff.mp hp ▸ hFD hzo)
      · have hwo : w ∈ Omega := ⟨mem_univ _, (mem_singleton_iff.mp hw.2).symm ▸ hs⟩
        have hzw := hFinj hwo hzo heq
        have hh := congrArg Prod.snd hzw
        exact hz.2.2.ne (hh.symm.trans (mem_singleton_iff.mp hw.2))
    have hcl : (q, s) ∈ closure (univ ×ˢ Ioo (-H) s) := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hs.1.ne]
      exact ⟨mem_univ _, hs.1.le, le_rfl⟩
    have hcont := (hFloc ⟨(q, s), mem_univ _, hs⟩).contMDiffAt.continuousAt
    have hout := closure_mono hbelow (hcont.continuousWithinAt.mem_closure_image hcl)
    simpa only [closure_compl] using hout
  have hinterior : interior (closure B) = B := by
    apply Subset.antisymm
    · intro x hx
      rcases hclosure ▸ interior_subset hx with hxB | hxS
      · exact hxB
      · exact False.elim (hSigmaNotInterior hxS hx)
    · exact hBopen.subset_interior_iff.mpr subset_closure
  have hfrontier : frontier (closure B) = Sigma s := by
    rw [frontier, closure_closure, hinterior, hclosure]
    ext x
    constructor
    · rintro ⟨hx | hx, hnot⟩
      · exact False.elim (hnot hx)
      · exact hx
    · intro hx
      refine ⟨Or.inr hx, ?_⟩
      intro hxB
      exact hSigmaNotInterior hx (hinterior.symm ▸ hxB)
  have hclSub : closure B ⊆ F '' Omega ∪ {p0} := by
    rw [hclosure]
    exact union_subset hBsub ((hSigmaSub hs).trans subset_union_left)
  refine ⟨hBopen, (hTconnected hs).subset_closure subset_union_left ?_,
    isClosed_closure.isCompact, hclosure, hinterior, hfrontier,
    haugDis.mono hclSub (image_mono hclSub), ?_⟩
  · rintro x (hx | hx)
    · exact subset_closure hx
    · exact (mem_singleton_iff.mp hx).symm ▸ hpcl
  · ext x
    constructor
    · intro hx hB
      have hxTail : x ∈ T s ∪ negE '' T s := by
        rcases hB with (hxT | hxp) | ⟨y, hyT | hyp, heq⟩
        · exact Or.inl hxT
        · exact False.elim (hp0D (mem_singleton_iff.mp hxp ▸ hx.1))
        · exact Or.inr ⟨y, hyT, heq⟩
        · subst y
          change -p0 = x at heq
          exact False.elim (hnegp0D (heq.symm ▸ hx.1))
      exact hx.2.2 ((hpairTail hs).symm.subset hxTail).2
    · intro hx
      have hxD : x ∈ D := by
        rw [hpairD]
        intro hp
        rcases hp with hp | hp
        · exact hx (Or.inl (Or.inr hp))
        · exact hx (Or.inr ⟨p0, Or.inr rfl, (mem_singleton_iff.mp hp).symm⟩)
      refine ⟨hxD, StandardPuncturedProjectiveCover.cover_mem P hxD, ?_⟩
      intro hreg
      rcases (hpairTail hs).subset ⟨hxD, hreg⟩ with ht | ht
      · exact hx (Or.inl (Or.inl ht))
      · exact hx (Or.inr (image_mono subset_union_left ht))

end PoincareConjecture.M25.Topology3D
