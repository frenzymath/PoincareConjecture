import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.RelativeInwardStripOpenness
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.MarkedCollarCompressionHomotopy
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.DomainProduct
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.Neighborhood
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Domains.CompactSubdomain
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

private theorem PLDomain.exists_compact_side_preserving_intersection
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heW : PLDomain e W)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source,y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source,y ∈ frontier W ↔ B y 1 = 0) :
    ∃ K : Set X, IsCompact K ∧ PLDomain e K ∧ K ⊆ W ∧
      D ∩ K = D ∩ W ∧
      (∀ x ∈ D ∩ W,x ∈ frontier K ↔ x ∈ frontier W) ∧
      ∀ x ∈ frontier D ∩ frontier K,
        ∃ B : OpenPartialHomeomorph X V3,
          x ∈ B.source ∧ B x = 0 ∧
          (∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ B.source,y ∈ frontier D ↔ B y 0 = 0) ∧
          ∀ y ∈ B.source,y ∈ frontier K ↔ B y 1 = 0 := by
  obtain ⟨K,V,hK,heK,hNK,hKW,hV,hNV,_,_,hfront,_⟩ :=
    heW.exists_compact_subdomain_near (hD.inter_right heW.closed)
      inter_subset_right isOpen_univ (subset_univ _)
  have hKW' : K ⊆ W := hKW.trans inter_subset_left
  have heq : D ∩ K = D ∩ W := Subset.antisymm
    (fun x hx => ⟨hx.1,hKW' hx.2⟩) (fun x hx => ⟨hx.1,hNK hx⟩)
  have hfrontV (x : X) (hx : x ∈ V) : x ∈ frontier K ↔ x ∈ frontier W :=
    ⟨fun h => (hfront.subset ⟨h,hx⟩).1,fun h => (hfront.symm.subset ⟨h,hx⟩).1⟩
  refine ⟨K,hK,heK,hKW',heq,fun x hx => hfrontV x (hNV hx),?_⟩
  intro x hx
  have hxN : x ∈ D ∩ W :=
    ⟨hD.isClosed.frontier_subset hx.1,hKW' (heK.closed.frontier_subset hx.2)⟩
  have hxV := hNV hxN
  obtain ⟨B,hxB,hB0,hcompat,hBD,hBW⟩ := hcross x
    ⟨hx.1,(hfrontV x hxV).mp hx.2⟩
  refine ⟨B.restrOpen V hV,⟨hxB,hxV⟩,hB0,?_,?_,?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hcompat i) hV
  · exact fun y hy => hBD y hy.1
  · exact fun y hy => (hfrontV y hy.2).trans (hBW y hy.1)

private theorem compress_disk_in_marked_face_model
    {X V α : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {E N S : Set X}
    (hNE : N ⊆ E)
    (K L : SimplicialComplex ℝ V) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (F : X → V) (g : V → X)
    (hF : ∀ i,LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hFN : MapsTo F N K.space) (hgN : MapsTo g K.space N)
    (hleft : ∀ x ∈ N,g (F x)=x)
    (c : V × ℝ → V) (hc : FinitePiecewiseAffineOn c (L.space ×ˢ I))
    (hci : InjOn c (L.space ×ˢ I)) (hcK : MapsTo c (L.space ×ˢ I) K.space)
    (hopen : IsOpen ((Subtype.val : K.space → V) ⁻¹' (c '' (L.space ×ˢ Ico 0 1))))
    (hbase : ∀ z ∈ K.space,g z ∈ frontier E → z ∈ c '' (L.space ×ˢ {(0 : ℝ)}))
    (hmark : ∀ z ∈ L.space ×ˢ I,g (c z) ∈ S ↔ g (c (z.1,0)) ∈ S)
    {d r : Set P2} (hd : IsFinitePLBallPair P2 d r)
    (q : P2 → X) (hq : PolyhedralPLInCharts e q d) (hqi : InjOn q d)
    (hqN : q '' d ⊆ N) (hqS : q '' d ∩ S = q '' r) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k d ∧ InjOn k d ∧
      k '' d ⊆ interior E ∧ k '' d ∩ S = k '' r ∧
      ∃ H : C(I × d,E),
        (∀ z : d,(H (0,z) : X)=q z) ∧
        (∀ z : d,(H (1,z) : X)=k z) ∧
        ∀ (t : I) (z : d),(H (t,z) : X) ∈ S ↔ (z : P2) ∈ r := by
  obtain ⟨D,A,hA,hDK,hclear,G,hG0,hG1,_,_,hGmark⟩ :=
    Dehn.exists_inward_collar_compression_homotopy K L hK hL c hc hci hcK hopen
  have hDint : g '' D ⊆ interior E := by
    rintro _ ⟨z,hz,rfl⟩
    have hgE : g z ∈ E := hNE (hgN (hDK hz))
    by_contra hnot
    obtain ⟨⟨w,t⟩,⟨hw,ht⟩,heq⟩ := hbase z (hDK hz) ⟨subset_closure hgE,hnot⟩
    have ht0 : t=0 := ht
    subst t
    have hh := (hclear (w,0) ⟨hw,by norm_num⟩).mp (heq.symm ▸ hz)
    norm_num at hh
  obtain ⟨a,ha,haval⟩ := hA
  have haD (z : V) (hz : z ∈ K.space) : a z ∈ D := haval ⟨z,hz⟩ ▸ (A ⟨z,hz⟩).property
  have hai : InjOn a K.space := by
    intro x hx y hy hh
    exact congrArg Subtype.val (A.injective (Subtype.ext
      ((haval ⟨x,hx⟩).trans (hh.trans (haval ⟨y,hy⟩).symm))))
  have hqF : MapsTo (F ∘ q) d K.space := fun z hz => hFN (hqN ⟨z,hz,rfl⟩)
  have hdCopy := hd
  obtain ⟨_,_,_,_,_,_,⟨_,⟨JJ,hJ,hJs,_⟩,_⟩,_⟩ := hdCopy
  have hFq : FinitePiecewiseAffineOn (F ∘ q) JJ.space :=
    (hJs.symm ▸ hq).finitePiecewiseAffineOn_comp JJ hJ hF
  have haq := ha.comp hFq (fun z hz => hqF (hJs.subset hz))
  let k : P2 → X := g ∘ a ∘ F ∘ q
  have hk : PolyhedralPLInCharts e k d := by
    rw [←hJs]
    exact hg.comp_finitePiecewiseAffineOn JJ hJ haq
      (fun z hz => hDK (haD _ (hqF (hJs.subset hz))))
  have hki : InjOn k d := by
    intro x hx y hy hh
    have hxy := hai (hqF hx) (hqF hy)
      (hgi (hDK (haD _ (hqF hx))) (hDK (haD _ (hqF hy))) hh)
    exact hqi hx hy ((hleft _ (hqN ⟨x,hx,rfl⟩)).symm.trans
      ((congrArg g hxy).trans (hleft _ (hqN ⟨y,hy,rfl⟩))))
  have hkE : k '' d ⊆ interior E := by
    rintro _ ⟨z,hz,rfl⟩
    exact hDint ⟨a (F (q z)),haD _ (hqF hz),rfl⟩
  let qK : C(d,K.space) := ⟨fun z => ⟨F (q z),hqF z.property⟩,
    (hJs ▸ hFq.continuousOn).domRestrict.subtype_mk _⟩
  let H : C(I × d,E) := ⟨fun z =>
    ⟨g (G (z.1,qK z.2)),hNE (hgN (G (z.1,qK z.2)).property)⟩,
    (hg.continuousOn.comp_continuous
      (continuous_subtype_val.comp (G.continuous.comp
        (continuous_fst.prodMk (qK.continuous.comp continuous_snd))))
      (fun z => (G (z.1,qK z.2)).property)).subtype_mk _⟩
  have hH0 (z : d) : (H (0,z) : X)=q z := by
    change g (G (0,qK z))=q z
    rw [hG0]
    exact hleft _ (hqN ⟨z,z.property,rfl⟩)
  have hH1 (z : d) : (H (1,z) : X)=k z := by
    change g (G (1,qK z))=k z
    rw [hG1,haval]
    rfl
  have hqr (z : d) : q z ∈ S ↔ (z : P2) ∈ r := by
    constructor
    · intro hz
      obtain ⟨w,hw,hh⟩ := hqS.subset ⟨mem_image_of_mem q z.property,hz⟩
      exact hqi (hd.1 hw) z.property hh ▸ hw
    · intro hz
      exact (hqS.symm.subset ⟨z,hz,rfl⟩).2
  have hHm (t : I) (z : d) : (H (t,z) : X) ∈ S ↔ (z : P2) ∈ r := by
    have hh := hGmark (g ⁻¹' S) {w | g (c (w,0)) ∈ S} hmark t (qK z)
    change g (G (t,qK z)) ∈ S ↔ g (F (q z)) ∈ S at hh
    rw [hleft _ (hqN ⟨z,z.property,rfl⟩)] at hh
    exact hh.trans (hqr z)
  refine ⟨k,hk,hki,hkE,?_,H,hH0,hH1,hHm⟩
  apply Subset.antisymm
  · rintro x ⟨⟨z,hz,rfl⟩,hs⟩
    exact ⟨z,(hHm 1 ⟨z,hz⟩).mp ((hH1 ⟨z,hz⟩).symm ▸ hs),rfl⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨mem_image_of_mem k (hd.1 hz),(hH1 ⟨z,hd.1 hz⟩) ▸ (hHm 1 ⟨z,hd.1 hz⟩).mpr hz⟩

theorem exists_original_relative_marked_disk_motion
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heD : PLDomain e D) (heW : PLDomain e W)
    (heN : PLDomain e (D ∩ W))
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source,y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source,y ∈ frontier W ↔ B y 1 = 0)
    {d r : Set P2} (hd : IsFinitePLBallPair P2 d r)
    (q : P2 → X) (hq : PolyhedralPLInCharts e q d) (hqi : InjOn q d)
    (hqN : q '' d ⊆ D ∩ W) (hqS : q '' d ∩ frontier W = q '' r) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k d ∧ InjOn k d ∧
      k '' d ⊆ interior D ∧ k '' d ∩ frontier W = k '' r ∧
      ∃ H : C(I × d,D),
        (∀ z : d,(H (0,z) : X)=q z) ∧
        (∀ z : d,(H (1,z) : X)=k z) ∧
        ∀ (t : I) (z : d),(H (t,z) : X) ∈ frontier W ↔ (z : P2) ∈ r := by
  classical
  obtain ⟨W',hW',heW',hWW,hNsame,hfrontW,hcrossW⟩ :=
    heW.exists_compact_side_preserving_intersection hD hcross
  obtain ⟨z,hz,_⟩ := hd.sdiff_nonempty
  have hne : (D ∪ W').Nonempty := ⟨q z,Or.inl (hqN ⟨z,hz,rfl⟩).1⟩
  obtain ⟨s,F,C,T,H,g,f,hC,hDC,hFc,hF,hTs,hM0,hM1,hM2,hM3,
      hHF,hgc,hg,hgPL,hgi,hleft,hright,hf,hfi,hfA,himage,hf0,hfW,hfD,hffD,hffW⟩ :=
    exists_signed_domain_surface_product hD heD hW' heW' hne hcrossW
  let V := s → ℝ × V3
  let N := D ∩ W
  let inv : V → X := fun z => g z
  have hNC : N ⊆ C := fun x hx => interior_subset (hDC (Or.inl hx.1))
  have hFinj : InjOn F C := by
    intro x hx y hy hh
    exact (hleft x hx).symm.trans ((congrArg inv hh).trans (hleft y hy))
  obtain ⟨K,_,_,hK,_,_,hKs,_,_,_⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair e heN.cover hFc hF
      (hD.inter_right heW.closed) (hFinj.mono hNC) heN.halfspace
  have hKA : K.space ⊆ T.ambient.space := by
    rw [hKs,hTs]
    exact image_mono hNC
  have hFN : MapsTo F N K.space := fun x hx => hKs.symm.subset ⟨x,hx,rfl⟩
  have hgN : MapsTo inv K.space N := by
    intro x hx
    obtain ⟨y,hy,hyx⟩ := hKs.subset hx
    change (g x : X) ∈ N
    rw [←hyx,hleft y (hNC hy)]
    exact hy
  have hgK : PolyhedralPLInCharts e inv K.space := hgPL.restrict_finite K hK hKA
  have hmem (x : V) (hx : x ∈ T.ambient.space) : x ∈ K.space ↔ inv x ∈ N := by
    refine ⟨fun h => hgN h,fun h => ?_⟩
    exact hKs.symm.subset ⟨inv x,h,hright x hx⟩
  have hK0 : K.space ⊆ (T.marked 0).space := by
    intro x hx
    exact hM0.symm.subset ⟨inv x,(hNsame.symm.subset (hgN hx)).2,hright x (hKA hx)⟩
  obtain ⟨O,hO,hSO,hON⟩ := T.exists_open_neighborhood_in_dual_union
  obtain ⟨A,hA,hAval⟩ := hf.exists_homeomorph_image hfi
  have hsign : ∀ z ∈ (T.marked 2).space ×ˢ J,f z ∈ K.space ↔ 0 ≤ z.2 := by
    intro z hz
    rw [hmem _ (hfA hz)]
    constructor
    · exact fun h => (hfD z hz).mp h.1
    · exact fun h => ⟨(hfD z hz).mpr h,hWW (hfW z hz)⟩
  obtain ⟨δ,hδ,hδsmall,hshort,hopen⟩ := exists_short_relative_inward_strip
    ((T.marked 2).isCompact_space_of_finite (T.marked_finite 2)) f hf.continuousOn
    A hAval hO (fun z hz => (hf0 z hz).symm ▸ hSO hz)
    (fun x hx => himage.symm.subset (hON ⟨hx.1,hK0 hx.2⟩)) hsign
  let scale : ℝ →ᴬ[ℝ] ℝ := δ • ContinuousAffineMap.id ℝ ℝ
  have hid : FinitePiecewiseAffineOn (id : V → V) (T.marked 2).space :=
    ⟨T.marked 2,T.marked_finite 2,rfl,
      (T.marked 2).affineOnFaces_affine (ContinuousAffineMap.id ℝ V)⟩
  obtain ⟨_,_,_,_,_,_,⟨_,⟨I0,hI0,hI0s,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ)<1 by norm_num)
  have hscale : FinitePiecewiseAffineOn scale I :=
    ⟨I0,hI0,hI0s,I0.affineOnFaces_affine scale⟩
  let c : V × ℝ → V := f ∘ Prod.map id scale
  have hparam (z : V × ℝ) (hz : z ∈ (T.marked 2).space ×ˢ I) :
      (z.1,δ*z.2) ∈ (T.marked 2).space ×ˢ J := by
    refine ⟨hz.1,?_,?_⟩
    · nlinarith [hz.2.1]
    · nlinarith [hz.2.2]
  have hc : FinitePiecewiseAffineOn c ((T.marked 2).space ×ˢ I) :=
    hf.comp (hid.prodMap hscale) hparam
  have hci : InjOn c ((T.marked 2).space ×ˢ I) := by
    intro z hz w hw hh
    have heq := hfi (hparam z hz) (hparam w hw) hh
    apply Prod.ext
    · simpa only using congrArg (fun x : V × ℝ => x.1) heq
    · exact mul_left_cancel₀ hδ.ne' (congrArg Prod.snd heq)
  have hcK : MapsTo c ((T.marked 2).space ×ˢ I) K.space :=
    fun z hz => (hsign _ (hparam z hz)).mpr (mul_nonneg hδ.le hz.2.1)
  have hstrip : c '' ((T.marked 2).space ×ˢ Ico 0 1) =
      f '' ((T.marked 2).space ×ˢ Ico 0 δ) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      exact ⟨(z,δ*t),⟨hz,mul_nonneg hδ.le ht.1,by nlinarith [ht.2]⟩,rfl⟩
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      refine ⟨(z,t/δ),⟨hz,div_nonneg ht.1 hδ.le,(div_lt_one hδ).mpr ht.2⟩,?_⟩
      change f (z,δ*(t/δ))=f (z,t)
      rw [mul_div_cancel₀ t hδ.ne']
  have hbase : ∀ z ∈ K.space,inv z ∈ frontier D →
      z ∈ c '' ((T.marked 2).space ×ˢ {(0 : ℝ)}) := by
    intro z hz hzD
    have hzL : z ∈ (T.marked 2).space :=
      hM2.symm.subset ⟨inv z,⟨hzD,(hNsame.symm.subset (hgN hz)).2⟩,hright z (hKA hz)⟩
    refine ⟨(z,0),⟨hzL,rfl⟩,?_⟩
    change f (z,δ*0)=z
    rw [mul_zero,hf0 z hzL]
  have hmark : ∀ z ∈ (T.marked 2).space ×ˢ I,
      inv (c z) ∈ frontier W ↔ inv (c (z.1,0)) ∈ frontier W := by
    intro z hz
    have hz0 : (z.1,0) ∈ (T.marked 2).space ×ˢ I := ⟨hz.1,by norm_num⟩
    have hceq : c (z.1,0)=z.1 := by
      change f (z.1,δ*0)=z.1
      rw [mul_zero,hf0 z.1 hz.1]
    rw [←hfrontW _ (hgN (hcK hz)),←hfrontW _ (hgN (hcK hz0))]
    rw [hceq]
    exact hffW _ (hparam z hz)
  exact compress_disk_in_marked_face_model inter_subset_left K (T.marked 2) hK
    (T.marked_finite 2) F inv hF hgK (hgi.mono hKA) hFN hgN
    (fun x hx => hleft x (hNC hx)) c hc hci hcK (hstrip.symm ▸ hopen)
    hbase hmark hd q hq hqi hqN hqS

end PoincareConjecture.M76
