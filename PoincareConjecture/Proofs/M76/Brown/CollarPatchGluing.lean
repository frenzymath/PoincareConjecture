import PoincareConjecture.Proofs.M76.Brown.CollarPatchAlignment
import PoincareConjecture.Proofs.M76.Mathlib.TorusCrossingBandImmersion

set_option autoImplicit false

open Set

namespace BrownCollar

private theorem exists_injective_union {Z X : Type*}
    [TopologicalSpace Z] [TopologicalSpace X] [Nonempty Z]
    (e d : OpenPartialHomeomorph Z X) (heq : EqOn e d (e.source ∩ d.source))
    (hcross : ∀ x ∈ e.source, ∀ y ∈ d.source, e x = d y → x = y) :
    ∃ c : OpenPartialHomeomorph Z X, c.source = e.source ∪ d.source ∧
      EqOn c e e.source ∧ EqOn c d d.source := by
  obtain ⟨F, hF, hFe, hFd⟩ := e.exists_union_localHomeomorph d heq
  let U := e.source ∪ d.source
  have hU : IsOpen U := e.open_source.union d.open_source
  have hFinj : InjOn F U := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact e.injOn hx hy (by simpa only [hFe hx, hFe hy] using hxy)
    · exact hcross x hx y hy (by simpa only [hFe hx, hFd hy] using hxy)
    · exact (hcross y hy x hx (by simpa only [hFe hy, hFd hx] using hxy.symm)).symm
    · exact d.injOn hx hy (by simpa only [hFd hx, hFd hy] using hxy)
  have hFlocal : IsLocalHomeomorph (U.domRestrict F) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hF.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun z _ => z.property))
  let c := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hFinj.toPartialEquiv F U) hF.continuousOn hFlocal.isOpenMap hU
  exact ⟨c, rfl, hFe, hFd⟩

variable {B X : Type*} [MetricSpace B] [LocallyCompactSpace B] [Nonempty B]
  [MetricSpace X]

theorem exists_collar_patch_union
    (c1 c2 : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) X)
    (i : B → X) (hi : Function.Injective i)
    {K1 K2 : Set B} (hK1 : IsCompact K1) (hK2 : IsCompact K2)
    (hsource1 : ∀ b ∈ K1, collarBase b ∈ c1.source)
    (hsource2 : ∀ b ∈ K2, collarBase b ∈ c2.source)
    (hbase1 : ∀ b, collarBase b ∈ c1.source → c1 (collarBase b) = i b)
    (hbase2 : ∀ b, collarBase b ∈ c2.source → c2 (collarBase b) = i b) :
    ∃ c : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) X,
      (∀ b ∈ K1 ∪ K2, collarBase b ∈ c.source) ∧
      ∀ b, collarBase b ∈ c.source → c (collarBase b) = i b := by
  classical
  let : Nonempty (B × Ico (0 : ℝ) 1) := ⟨collarBase (Classical.arbitrary B)⟩
  obtain ⟨d, hdS, _, hdbase, V, hV, hKV, hVS, hagree⟩ :=
    exists_collar_patch_alignment c1 c2 i (hK1.inter_right hK2.isClosed)
      (fun b hb => hsource1 b hb.1) (fun b hb => hsource2 b hb.2) hbase1 hbase2
  have hsourceD (b : B) (hb : b ∈ K2) : collarBase b ∈ d.source :=
    hdS.symm ▸ hsource2 b hb
  have hbcont : Continuous (collarBase : B → B × Ico (0 : ℝ) 1) :=
    continuous_id.prodMk continuous_const
  let E1 := (collarBase '' K1) \ V
  let E2 := (collarBase '' K2) \ V
  have hE1 : IsCompact E1 := (hK1.image hbcont).diff hV
  have hE2 : IsCompact E2 := (hK2.image hbcont).diff hV
  have hE1S : E1 ⊆ c1.source := by
    rintro z ⟨⟨b, hb, rfl⟩, _⟩
    exact hsource1 b hb
  have hE2S : E2 ⊆ d.source := by
    rintro z ⟨⟨b, hb, rfl⟩, _⟩
    exact hsourceD b hb
  have hEdisj : Disjoint E1 E2 := by
    apply disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨b, hb, rfl⟩ := hz1.1
    obtain ⟨a, ha, hab⟩ := hz2.1
    have he : a = b := congrArg Prod.fst hab
    exact hz1.2 (hKV ⟨b, ⟨hb, he ▸ ha⟩, rfl⟩)
  have hImage1 : IsCompact (c1 '' E1) :=
    hE1.image_of_continuousOn (c1.continuousOn.mono hE1S)
  have hImage2 : IsCompact (d '' E2) :=
    hE2.image_of_continuousOn (d.continuousOn.mono hE2S)
  have hImageDisj : Disjoint (c1 '' E1) (d '' E2) := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ ⟨w, hw, hvalue⟩
    obtain ⟨b, hb, rfl⟩ := hz.1
    obtain ⟨a, ha, rfl⟩ := hw.1
    have hab : a = b := hi ((hdbase a (hE2S hw)).symm.trans
      (hvalue.trans (hbase1 b (hE1S hz))))
    exact hz.2 (hKV ⟨b, ⟨hb, hab ▸ ha⟩, rfl⟩)
  obtain ⟨P1, P2, hP1, hP2, hE1P, hE2P, hPdisj⟩ :=
    normal_separation hE1.isClosed hE2.isClosed hEdisj
  obtain ⟨R1, R2, hR1, hR2, hE1R, hE2R, hRdisj⟩ :=
    normal_separation hImage1.isClosed hImage2.isClosed hImageDisj
  let V1 := P1 ∩ (c1.source ∩ c1 ⁻¹' R1)
  let V2 := P2 ∩ (d.source ∩ d ⁻¹' R2)
  have hV1 : IsOpen V1 := hP1.inter
    (c1.continuousOn.isOpen_inter_preimage c1.open_source hR1)
  have hV2 : IsOpen V2 := hP2.inter
    (d.continuousOn.isOpen_inter_preimage d.open_source hR2)
  have hE1V : E1 ⊆ V1 := fun z hz => ⟨hE1P hz, hE1S hz, hE1R ⟨z, hz, rfl⟩⟩
  have hE2V : E2 ⊆ V2 := fun z hz => ⟨hE2P hz, hE2S hz, hE2R ⟨z, hz, rfl⟩⟩
  let A1 := V1 ∪ V
  let A2 := V2 ∪ V
  have hA1 : IsOpen A1 := hV1.union hV
  have hA2 : IsOpen A2 := hV2.union hV
  have hA1S : A1 ⊆ c1.source := by
    rintro z (hz | hz)
    · exact hz.2.1
    · exact (hVS hz).1
  have hA2S : A2 ⊆ d.source := by
    rintro z (hz | hz)
    · exact hz.2.1
    · exact (hVS hz).2
  let e1 := c1.restr A1
  let e2 := d.restr A2
  have he1S : e1.source = A1 := by
    change c1.source ∩ interior A1 = A1
    rw [hA1.interior_eq, inter_eq_right.mpr hA1S]
  have he2S : e2.source = A2 := by
    change d.source ∩ interior A2 = A2
    rw [hA2.interior_eq, inter_eq_right.mpr hA2S]
  have heq : EqOn e1 e2 (e1.source ∩ e2.source) := by
    intro z hz
    have hz1 : z ∈ A1 := he1S ▸ hz.1
    have hz2 : z ∈ A2 := he2S ▸ hz.2
    rcases hz1 with hz1 | hzV
    · rcases hz2 with hz2 | hzV
      · exact (disjoint_left.mp hPdisj hz1.1 hz2.1).elim
      · exact hagree hzV
    · exact hagree hzV
  have hcross : ∀ x ∈ e1.source, ∀ y ∈ e2.source, e1 x = e2 y → x = y := by
    intro x hx y hy hxy
    have hx1 : x ∈ A1 := he1S ▸ hx
    have hy2 : y ∈ A2 := he2S ▸ hy
    change c1 x = d y at hxy
    by_cases hxV : x ∈ V
    · exact d.injOn (hVS hxV).2 (hA2S hy2) ((hagree hxV).symm.trans hxy)
    by_cases hyV : y ∈ V
    · exact c1.injOn (hA1S hx1) (hVS hyV).1 (hxy.trans (hagree hyV).symm)
    have hxV1 : x ∈ V1 := hx1.resolve_right hxV
    have hyV2 : y ∈ V2 := hy2.resolve_right hyV
    exact (disjoint_left.mp hRdisj (hxy ▸ hxV1.2.2) hyV2.2.2).elim
  obtain ⟨c, hcS, hce1, hce2⟩ := exists_injective_union e1 e2 heq hcross
  refine ⟨c, ?_, ?_⟩
  · intro b hb
    rw [hcS, he1S, he2S]
    rcases hb with hb | hb
    · apply Or.inl
      by_cases hbV : collarBase b ∈ V
      · exact Or.inr hbV
      · exact Or.inl (hE1V ⟨⟨b, hb, rfl⟩, hbV⟩)
    · apply Or.inr
      by_cases hbV : collarBase b ∈ V
      · exact Or.inr hbV
      · exact Or.inl (hE2V ⟨⟨b, hb, rfl⟩, hbV⟩)
  · intro b hb
    have hb' : collarBase b ∈ e1.source ∪ e2.source := hcS ▸ hb
    rcases hb' with hb' | hb'
    · exact (hce1 hb').trans (hbase1 b (hA1S (he1S ▸ hb')))
    · exact (hce2 hb').trans (hdbase b (hA2S (he2S ▸ hb')))

end BrownCollar
