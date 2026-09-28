import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Noncollapse
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.NeckPatch
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Curvature
import Mathlib.Topology.Homeomorph.Lemmas


















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

private noncomputable def seedZeroCylinder
    (F : GeneralizedRicciFlowData.{u}) (t q : ℝ) (hq : 0 < q)
    (W : Set (F.slice t).carrier) :
    GeneralizedFlowCylinder F (F.slice t) t q ({0} : Set ℝ) W := by
  let hclock (s : ℝ) (hs : s ∈ ({0} : Set ℝ)) : t + s / q = t := by
    rw [mem_singleton_iff.mp hs]
    simp only [zero_div, add_zero]
  let transport {a b : ℝ} (h : a = b) :
      (F.slice a).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (F.slice b).carrier :=
    h ▸ Diffeomorph.refl (𝓡 3) (F.slice a).carrier ∞
  let e (s : ℝ) (hs : s ∈ ({0} : Set ℝ)) := transport (hclock s hs).symm
  have hpoint {a b : ℝ} (h : a = b) (x : (F.slice a).carrier) :
      (⟨b, transport h x⟩ : F.point) = ⟨a, x⟩ := by
    cases h
    rfl
  refine {
    scale_pos := hq
    forward := fun s hs => e s hs
    inverse := fun s hs => (e s hs).symm
    forward_smooth := fun s hs => (e s hs).contMDiff.contMDiffOn
    inverse_smooth := fun s hs => (e s hs).symm.contMDiff.contMDiffOn
    left_inverse := fun s hs x _ => (e s hs).left_inv x
    right_inverse := fun s hs x _ => (e s hs).right_inv x
    embedding := ?_
    vertical_compatibility := ?_ }
  · have he := (F.slice_embedding t).comp (Topology.IsEmbedding.subtypeVal (p := W))
    have hh := he.comp (Homeomorph.uniqueProd ↥({0} : Set ℝ) W).isEmbedding
    convert! hh using 1
    funext p
    exact hpoint (hclock p.1.1 p.1.2).symm p.2.1
  · intro s hs x _hx
    obtain ⟨b, ht, y, hy⟩ := F.box_covers (t + s / q) (e s hs x)
    refine ⟨b, y, 1, zero_lt_one, ?_⟩
    intro s' hs' _hnear
    have hs0 : s' = s := (mem_singleton_iff.mp hs').trans (mem_singleton_iff.mp hs).symm
    cases hs0
    exact ⟨ht, hy.symm⟩

private theorem seedZeroCylinder_pointMap
    (F : GeneralizedRicciFlowData.{u}) (t q : ℝ) (hq : 0 < q)
    (W : Set (F.slice t).carrier) (hzero : (0 : ℝ) ∈ ({0} : Set ℝ))
    (x : (F.slice t).carrier) :
    (seedZeroCylinder F t q hq W).pointMap 0 hzero x = (⟨t, x⟩ : F.point) := by
  let transport {a b : ℝ} (h : a = b) :
      (F.slice a).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (F.slice b).carrier :=
    h ▸ Diffeomorph.refl (𝓡 3) (F.slice a).carrier ∞
  have hcast {a b : ℝ} (h : a = b) (y : (F.slice a).carrier) :
      (⟨b, transport h y⟩ : F.point) = ⟨a, y⟩ := by
    cases h
    rfl
  exact hcast _ x

private theorem glue_terminal_cylinders_on_compact_source
    {F : GeneralizedRicciFlowData.{u}} {origin q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) {U : Set (F.slice origin).carrier} {ι : Type*}
    (hU : IsOpen U) (hne : U.Nonempty) (hcompact : IsCompact (closure U))
    (V : ι → Set (F.slice origin).carrier)
    (d : ∀ i, GeneralizedFlowCylinder F (F.slice origin) origin q (Icc (-c) 0) (V i))
    (hV : ∀ i, IsOpen (V i)) (hcover : ∀ x ∈ closure U, ∃ i, x ∈ V i)
    (hanchor : ∀ i x, x ∈ V i →
      (d i).pointMap 0 ⟨by linarith, le_rfl⟩ x = (⟨origin, x⟩ : F.point)) :
    ∃ g : GeneralizedFlowCylinder F (F.slice origin) origin q (Icc (-c) 0) U,
      (∀ hzero x, x ∈ U → g.pointMap 0 hzero x = (⟨origin, x⟩ : F.point)) ∧
      (∀ i s hs x, x ∈ U → x ∈ V i → g.pointMap s hs x = (d i).pointMap s hs x) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  let K := closure U
  let pick : K → ι := fun x => Classical.choose (hcover x.1 x.2)
  have hpick (x : K) : x.1 ∈ V (pick x) := Classical.choose_spec (hcover x.1 x.2)
  let retain : (F.slice origin).carrier → K := fun x =>
    if hx : x ∈ K then ⟨x, hx⟩ else ⟨x₀, subset_closure hx₀⟩
  have hretain {x : (F.slice origin).carrier} (hx : x ∈ K) : (retain x).1 = x := by
    simp only [retain, dif_pos hx]
  let f : ∀ s, s ∈ Icc (-c) 0 → (F.slice origin).carrier →
      (F.slice (origin + s / q)).carrier :=
    fun s hs x => (d (pick (retain x))).forward s hs (retain x).1
  have hfpatch (i : ι) (s : ℝ) (hs : s ∈ Icc (-c) 0)
      {x : (F.slice origin).carrier} (hx : x ∈ K) (hxi : x ∈ V i) :
      f s hs x = (d i).forward s hs x := by
    have hxj : x ∈ V (pick (retain x)) := by
      simpa only [retain, dif_pos hx] using hpick (⟨x, hx⟩ : K)
    have heq := cylinder_pointMap_eq_on_interval (d (pick (retain x))) (d i)
      ordConnected_Icc hxj hxi (s := 0) ⟨by linarith, le_rfl⟩
      ((hanchor _ x hxj).trans (hanchor i x hxi).symm) s hs
    dsimp only [f]
    rw [hretain hx]
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  have hinj (s : ℝ) (hs : s ∈ Icc (-c) 0) : InjOn (f s hs) K := by
    intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := hcover x hx
    obtain ⟨j, hyj⟩ := hcover y hy
    rw [hfpatch i s hs hx hxi, hfpatch j s hs hy hyj] at hxy
    have heq := cylinder_pointMap_eq_on_interval (d i) (d j) ordConnected_Icc
      hxi hyj hs (congrArg (fun z => (⟨origin + s / q, z⟩ : F.point)) hxy)
      0 ⟨by linarith, le_rfl⟩
    rw [hanchor i x hxi, hanchor j y hyj] at heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  let G : Icc (-c) 0 × K → F.point := fun p => ⟨origin + p.1.1 / q, f p.1.1 p.1.2 p.2.1⟩
  have hGinj : Function.Injective G := by
    rintro ⟨s, x⟩ ⟨r, y⟩ heq
    have hsr : s.1 = r.1 := by
      have ht := congrArg Sigma.fst heq
      change origin + s.1 / q = origin + r.1 / q at ht
      exact (div_left_inj' hq.ne').mp (add_left_cancel ht)
    have hsub : s = r := Subtype.ext hsr
    subst r
    exact Prod.ext rfl (Subtype.ext (hinj s.1 s.2 x.2 y.2
      (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)))
  have hGcont : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨i, hpi⟩ := hcover p.2.1 p.2.2
    let O : Set (Icc (-c) 0 × K) := {z | z.2.1 ∈ V i}
    have hO : IsOpen O :=
      (hV i).preimage (continuous_subtype_val.comp continuous_snd)
    let H : O → Icc (-c) 0 × V i := fun z => (z.1.1, ⟨z.1.2.1, z.2⟩)
    have hH : Continuous H :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk
          (fun z => z.2))
    have hcont : Continuous (fun z : O => G z.1) := by
      convert (d i).embedding.continuous.comp hH using 1
      funext z
      exact congrArg (fun w => (⟨origin + z.1.1.1 / q, w⟩ : F.point))
        (hfpatch i z.1.1.1 z.1.1.2 z.1.2.2 z.2)
    exact (continuousOn_iff_continuous_domRestrict.mpr hcont).continuousAt
      (hO.mem_nhds hpi)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  have : CompactSpace (Icc (-c) 0) := isCompact_iff_compactSpace.mp isCompact_Icc
  have : T2Space F.point := F.space_t2
  have hGemb : Topology.IsEmbedding G := (hGcont.isClosedEmbedding hGinj).isEmbedding
  have hfsmooth (s : ℝ) (hs : s ∈ Icc (-c) 0) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) U := by
    intro x hx
    obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
    apply ContMDiffAt.contMDiffWithinAt
    apply ((d i).forward_smooth s hs).contMDiffAt ((hV i).mem_nhds hxi)
      |>.congr_of_eventuallyEq
    filter_upwards [(hU.inter (hV i)).mem_nhds ⟨hx, hxi⟩] with y hy
    exact hfpatch i s hs (subset_closure hy.1) hy.2
  let inv : ∀ s, s ∈ Icc (-c) 0 → (F.slice (origin + s / q)).carrier →
      (F.slice origin).carrier :=
    fun s hs y => if hy : y ∈ f s hs '' U then Classical.choose hy else x₀
  have hleft (s : ℝ) (hs : s ∈ Icc (-c) 0) : LeftInvOn (inv s hs) (f s hs) U := by
    intro x hx
    have hi : f s hs x ∈ f s hs '' U := mem_image_of_mem _ hx
    simp only [inv, dif_pos hi]
    exact hinj s hs (subset_closure (Classical.choose_spec hi).1) (subset_closure hx)
      (Classical.choose_spec hi).2
  have hright (s : ℝ) (hs : s ∈ Icc (-c) 0) :
      LeftInvOn (f s hs) (inv s hs) (f s hs '' U) := by
    intro y hy
    simp only [inv, dif_pos hy]
    exact (Classical.choose_spec hy).2
  have hismooth (s : ℝ) (hs : s ∈ Icc (-c) 0) :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inv s hs) (f s hs '' U) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
    have hfx := hfpatch i s hs (subset_closure hx) hxi
    have hopen := cylinder_isOpen_forward_image
      ((d i).restrict Subset.rfl inter_subset_right) (hU.inter (hV i)) s hs
    change IsOpen ((d i).forward s hs '' (U ∩ V i)) at hopen
    have hmem : f s hs x ∈ (d i).forward s hs '' (U ∩ V i) :=
      ⟨x, ⟨hx, hxi⟩, hfx.symm⟩
    have hwhole := cylinder_isOpen_forward_image (d i) (hV i) s hs
    have hwholemem : f s hs x ∈ (d i).forward s hs '' V i := ⟨x, hxi, hfx.symm⟩
    apply ContMDiffAt.contMDiffWithinAt
    apply ((d i).inverse_smooth s hs).contMDiffAt (hwhole.mem_nhds hwholemem)
      |>.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rcases hz with ⟨w, hw, rfl⟩
    rw [← hfpatch i s hs (subset_closure hw.1) hw.2, hleft s hs hw.1]
    rw [hfpatch i s hs (subset_closure hw.1) hw.2]
    exact ((d i).left_inverse s hs hw.2).symm
  have hvert (s : ℝ) (hs : s ∈ Icc (-c) 0) (x : (F.slice origin).carrier) (hx : x ∈ U) :
      ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ delta : ℝ, 0 < delta ∧
        ∀ s' (hs' : s' ∈ Icc (-c) 0), |s' - s| < delta →
          ∃ hb : origin + s' / q ∈ (F.box b).interval,
            f s' hs' x = (F.box b).forward (origin + s' / q) hb y := by
    obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
    obtain ⟨b, y, delta, hdelta, hv⟩ := (d i).vertical_compatibility s hs x hxi
    refine ⟨b, y, delta, hdelta, ?_⟩
    intro s' hs' hnear
    obtain ⟨hb, heq⟩ := hv s' hs' hnear
    exact ⟨hb, (hfpatch i s' hs' (subset_closure hx) hxi).trans heq⟩
  let g : GeneralizedFlowCylinder F (F.slice origin) origin q (Icc (-c) 0) U := {
    scale_pos := hq
    forward := f
    inverse := inv
    forward_smooth := hfsmooth
    inverse_smooth := hismooth
    left_inverse := hleft
    right_inverse := hright
    embedding := hGemb.comp
      (Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion subset_closure))
    vertical_compatibility := hvert }
  refine ⟨g, ?_, ?_⟩
  · intro hzero x hx
    obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
    exact (congrArg (fun z => (⟨origin + 0 / q, z⟩ : F.point))
      (hfpatch i 0 hzero (subset_closure hx) hxi)).trans (hanchor i x hxi)
  · intro i s hs x hx hxi
    exact congrArg (fun z => (⟨origin + s / q, z⟩ : F.point))
      (hfpatch i s hs (subset_closure hx) hxi)

private theorem seed_native_time_mem_half
    {q R M c s : ℝ} (hq : 0 < q) (hR : 0 < R) (hM : 0 < M)
    (hc : 0 < c) (hcM : c ≤ 1 / (4 * M)) (hRbound : R ≤ M * q)
    (hs : s ∈ Icc (-c) 0) : s * R / q ∈ Icc (-(1 / 2 : ℝ)) 0 := by
  have hc4 : c * (4 * M) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4 * M)).mp hcM
  have hbound : (-s) * R ≤ c * (M * q) :=
    (mul_le_mul_of_nonneg_right (by linarith [hs.1]) hR.le).trans
      (mul_le_mul_of_nonneg_left hRbound hc.le)
  have hquarter : c * (M * q) ≤ q / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hc4 hq.le]
  refine ⟨(le_div_iff₀ hq).mpr ?_,
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hs.2 hR.le) hq.le⟩
  nlinarith [hbound.trans hquarter]





theorem exists_seed_cylinder_of_terminal_strongNecks
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilonSeed Kseed : ℝ, 0 < epsilonSeed ∧ epsilonSeed ≤ 1 / 200 ∧ 0 < Kseed ∧
      ∀ {M B c : ℝ}, 0 < M → 0 ≤ B → Kseed * M ≤ B → 0 < c → c ≤ 1 / (4 * M) →
      ∀ {F : GeneralizedRicciFlowData.{u}} {t q : ℝ}, 0 < q →
      ∀ {U W : Set (F.slice t).carrier},
        IsOpen U → IsOpen W → U.Nonempty → IsCompact (closure U) → closure U ⊆ W →
        (∀ x ∈ W, F.scalar ⟨t, x⟩ ≤ M * q) →
        (∀ x ∈ closure U, ∃ epsilon, epsilon ≤ epsilonSeed ∧
          ∃ N : GeneralizedStrongNeck F t epsilon, N.center = x) →
        ∃ g : GeneralizedFlowCylinder F (F.slice t) t q (Icc (-c) 0) U,
          (∀ hzero x, x ∈ U → g.pointMap 0 hzero x = (⟨t, x⟩ : F.point)) ∧
          (∀ s hs x, x ∈ U → F.scalar (g.pointMap s hs x) ≤ M * q) ∧
          (∀ s hs x, x ∈ U → |F.curvatureNorm (g.pointMap s hs x)| ≤ B * q) ∧
          (∀ s hs x, x ∈ U → GeneralizedKappaNoncollapsedAt F
            (g.pointMap s hs x) neckNoncollapseConstant 1) := by
  obtain ⟨epsilonR, Kseed, hRpos, hRsmall, hK, hcurvature⟩ :=
    exists_strongNeck_backward_curvature_bound.{u}
  obtain ⟨epsilonS, hSpos, _hSsmall, hscalarNeck⟩ :=
    exists_strongNeck_backward_scalarDerivative_comparison hM04
  obtain ⟨epsilonNC, hNCpos, _hNCsmall, hnoncollapse⟩ :=
    exists_strongNeck_backward_center_noncollapsed.{u}
  refine ⟨min epsilonR (min epsilonS epsilonNC), Kseed,
    lt_min hRpos (lt_min hSpos hNCpos), (min_le_left _ _).trans hRsmall, hK, ?_⟩
  intro M B c hM _hB hKM hc hcM F t q hq U W hU hW hne hcompact hKW hscalar hneck
  let e₀ := seedZeroCylinder F t q hq W
  have hzero : (0 : ℝ) ∈ ({0} : Set ℝ) := mem_singleton 0
  have hneck' : ∀ x ∈ closure U, ∃ epsilon, epsilon ≤ min epsilonR (min epsilonS epsilonNC) ∧
      ∃ N : GeneralizedStrongNeck F (t + 0 / q) epsilon, N.center = e₀.forward 0 hzero x := by
    have htransport {a b epsilon : ℝ} (h : a = b)
        (N : GeneralizedStrongNeck F a epsilon) (y : (F.slice b).carrier)
        (hy : HEq y N.center) :
        ∃ N' : GeneralizedStrongNeck F b epsilon, N'.center = y := by
      cases h
      exact ⟨N, (eq_of_heq hy).symm⟩
    intro x hx
    obtain ⟨epsilon, hepsilon, N, hcenter⟩ := hneck x hx
    refine ⟨epsilon, hepsilon, htransport (by simp : t = t + 0 / q) N
      (e₀.forward 0 hzero x) ?_⟩
    rw [hcenter]
    exact (Sigma.mk.inj_iff.mp (seedZeroCylinder_pointMap F t q hq W hzero x)).2
  choose epsilon hepsilon N hcenter using fun x : closure U => hneck' x.1 x.2
  let V : closure U → Set (F.slice t).carrier :=
    fun i => W ∩ (e₀.forward 0 hzero) ⁻¹' (N i).carrier
  have hV (i : closure U) : IsOpen (V i) :=
    (e₀.forward_smooth 0 hzero).continuousOn.isOpen_inter_preimage hW (N i).carrier_open
  have hcover : ∀ x ∈ closure U, ∃ i, x ∈ V i := by
    intro x hx
    refine ⟨⟨x, hx⟩, hKW hx, ?_⟩
    change e₀.forward 0 hzero x ∈ (N ⟨x, hx⟩).carrier
    rw [← hcenter ⟨x, hx⟩]
    exact (N ⟨x, hx⟩).central_sphere_subset (N ⟨x, hx⟩).center_on_central_sphere
  have hRbound (i : closure U) : (N i).scale⁻¹ ^ 2 ≤ M * q := by
    have hscale : (N i).scale =
        (Real.sqrt ((F.connection (t + 0 / q)).scalarCurvature (N i).center))⁻¹ := by
      rw [(N i).scale_scalar, neg_div, Real.rpow_neg (N i).scalar_center_pos.le,
        Real.sqrt_eq_rpow]
    rw [hscale, inv_inv, Real.sq_sqrt (N i).scalar_center_pos.le, hcenter i]
    change F.scalar (e₀.pointMap 0 hzero i.1) ≤ M * q
    rw [seedZeroCylinder_pointMap]
    exact hscalar i.1 (hKW i.2)
  have hhalf (i : closure U) : ∀ s ∈ Icc (-c) 0,
      (s - 0) * ((N i).scale⁻¹ ^ 2) / q ∈ Icc (-(1 / 2 : ℝ)) 0 := by
    intro s hs
    simpa only [sub_zero] using seed_native_time_mem_half hq
      (sq_pos_of_pos (inv_pos.mpr (N i).scale_pos)) hM hc hcM (hRbound i) hs
  have hnative (i : closure U) : ∀ s ∈ Icc (-c) 0,
      (s - 0) * ((N i).scale⁻¹ ^ 2) / q ∈ Ioc (-1) 0 := by
    intro s hs
    exact ⟨lt_of_lt_of_le (by norm_num) (hhalf i s hs).1, (hhalf i s hs).2⟩
  let d (i : closure U) : GeneralizedFlowCylinder F (F.slice t) t q (Icc (-c) 0) (V i) :=
    strongNeckAttachedCylinder e₀ hW hzero (N i) (hnative i)
  have hanchor (i : closure U) (x : (F.slice t).carrier) (hx : x ∈ V i) :
      (d i).pointMap 0 ⟨by linarith, le_rfl⟩ x = (⟨t, x⟩ : F.point) := by
    rw [strongNeckAttachedCylinder_pointMap]
    have hid (r : ℝ) (hr : r ∈ Ioc (-1) 0) (hr0 : r = 0) :
        (N i).time_cylinder.pointMap r hr (e₀.forward 0 hzero x) = e₀.pointMap 0 hzero x := by
      subst r
      exact (N i).cylinder_identity hr (e₀.forward 0 hzero x) hx.2
    exact (hid _ _ (by ring)).trans (seedZeroCylinder_pointMap F t q hq W hzero x)
  obtain ⟨g, hgzero, hgpatch⟩ := glue_terminal_cylinders_on_compact_source hq hc
    hU hne hcompact V d hV hcover hanchor
  refine ⟨g, hgzero, ?_, ?_, ?_⟩
  · intro s hs x hx
    obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
    rw [hgpatch i s hs x hx hxi, strongNeckAttachedCylinder_pointMap]
    have h := ((hscalarNeck (N i)
      ((hepsilon i).trans ((min_le_right _ _).trans (min_le_left _ _)))
      (e₀.forward 0 hzero x) hxi.2).2.2 _ (hnative i s hs))
    change F.scalar _ ≤ F.scalar (e₀.pointMap 0 hzero x) at h
    rw [seedZeroCylinder_pointMap] at h
    exact h.trans (hscalar x hxi.1)
  · intro s hs x hx
    obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
    rw [hgpatch i s hs x hx hxi, strongNeckAttachedCylinder_pointMap]
    calc
      _ ≤ Kseed * ((N i).scale⁻¹ ^ 2) := hcurvature (N i)
        ((hepsilon i).trans (min_le_left _ _)) (hnative i s hs) (e₀.forward 0 hzero x) hxi.2
      _ ≤ Kseed * (M * q) := mul_le_mul_of_nonneg_left (hRbound i) hK.le
      _ = (Kseed * M) * q := (mul_assoc _ _ _).symm
      _ ≤ B * q := mul_le_mul_of_nonneg_right hKM hq.le
  · intro s hs x hx
    let i : closure U := ⟨x, subset_closure hx⟩
    have hxi : x ∈ V i := by
      refine ⟨hKW (subset_closure hx), ?_⟩
      change e₀.forward 0 hzero x ∈ (N i).carrier
      rw [← hcenter i]
      exact (N i).central_sphere_subset (N i).center_on_central_sphere
    rw [hgpatch i s hs x hx hxi, strongNeckAttachedCylinder_pointMap, ← hcenter i]
    exact hnoncollapse (N i)
      ((hepsilon i).trans ((min_le_right _ _).trans (min_le_right _ _)))
      (hnative i s hs) (hhalf i s hs).1

end PoincareConjecture.M32
