import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Curvature
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.NeckPatch


















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

private theorem glue_cylinders_on_compact_source
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin q T L a : ℝ} {U W : Set C.carrier} {ι : Type*}
    (e : GeneralizedFlowCylinder F C origin q (Icc (-T) 0) W)
    (hU : IsOpen U) (hW : IsOpen W) (hne : U.Nonempty)
    (hcompact : IsCompact (closure U)) (hKW : closure U ⊆ W)
    (hL : L ≤ -T) (ha : -T < a) (ha0 : a ≤ 0)
    (V : ι → Set C.carrier)
    (d : ∀ i, GeneralizedFlowCylinder F C origin q (Icc L a) (V i))
    (hV : ∀ i, IsOpen (V i))
    (hcover : ∀ x ∈ closure U, ∃ i, x ∈ V i)
    (hanchor : ∀ i x, x ∈ V i →
      (d i).pointMap a ⟨hL.trans ha.le, le_rfl⟩ x =
        e.pointMap a ⟨ha.le, ha0⟩ x) :
    ∃ g : GeneralizedFlowCylinder F C origin q (Icc L 0) U,
      (∀ s (hs : s ∈ Icc (-T) 0) x, x ∈ U →
        g.pointMap s ⟨hL.trans hs.1, hs.2⟩ x = e.pointMap s hs x) ∧
      (∀ s (hs : s ∈ Icc L 0) (hsa : s ≤ a), ∀ x, x ∈ U →
        ∃ i, x ∈ V i ∧ g.pointMap s hs x = (d i).pointMap s ⟨hs.1, hsa⟩ x) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  let K := closure U
  let pick : K → ι := fun x => Classical.choose (hcover x.1 x.2)
  have hpick (x : K) : x.1 ∈ V (pick x) := Classical.choose_spec (hcover x.1 x.2)
  let retain : C.carrier → K := fun x =>
    if hx : x ∈ K then ⟨x, hx⟩ else ⟨x₀, subset_closure hx₀⟩
  have hretain {x : C.carrier} (hx : x ∈ K) : (retain x).1 = x := by
    simp only [retain, dif_pos hx]
  let f : ∀ s, s ∈ Icc L 0 → C.carrier → (F.slice (origin + s / q)).carrier :=
    fun s hs x => if hsa : s ≤ a then
      (d (pick (retain x))).forward s ⟨hs.1, hsa⟩ (retain x).1
    else e.forward s ⟨ha.le.trans (le_of_lt (lt_of_not_ge hsa)), hs.2⟩ x
  have hfpatch (i : ι) (s : ℝ) (hs : s ∈ Icc L a) {x : C.carrier}
      (hx : x ∈ K) (hxi : x ∈ V i) :
      f s ⟨hs.1, hs.2.trans ha0⟩ x = (d i).forward s hs x := by
    have hxj : x ∈ V (pick (retain x)) := by
      simpa only [retain, dif_pos hx] using hpick (⟨x, hx⟩ : K)
    have heq := cylinder_pointMap_eq_on_interval (d (pick (retain x))) (d i)
      ordConnected_Icc hxj hxi (s := a) ⟨hL.trans ha.le, le_rfl⟩
      ((hanchor _ x hxj).trans (hanchor i x hxi).symm) s hs
    dsimp only [f]
    rw [dif_pos hs.2, hretain hx]
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  have hfold (s : ℝ) (hs : s ∈ Icc (-T) 0) {x : C.carrier} (hx : x ∈ K) :
      f s ⟨hL.trans hs.1, hs.2⟩ x = e.forward s hs x := by
    by_cases hsa : s ≤ a
    · let i := pick (retain x)
      have hxi : x ∈ V i := by
        simpa only [i, retain, dif_pos hx] using hpick (⟨x, hx⟩ : K)
      rw [hfpatch i s ⟨hL.trans hs.1, hsa⟩ hx hxi]
      exact eq_of_heq (Sigma.mk.inj_iff.mp
        (cylinder_pointMap_eq_on_overlap (d i) e ordConnected_Icc ordConnected_Icc
          hxi (hKW hx) (s := a) ⟨hL.trans ha.le, le_rfl⟩ ⟨ha.le, ha0⟩
          (hanchor i x hxi) s ⟨hL.trans hs.1, hsa⟩ hs)).2
    · simp only [f, dif_neg hsa]
  have hinj (s : ℝ) (hs : s ∈ Icc L 0) : InjOn (f s hs) K := by
    intro x hx y hy hxy
    by_cases hsa : s ≤ a
    · let i := pick (retain x)
      let j := pick (retain y)
      have hxi : x ∈ V i := by
        simpa only [i, retain, dif_pos hx] using hpick (⟨x, hx⟩ : K)
      have hyj : y ∈ V j := by
        simpa only [j, retain, dif_pos hy] using hpick (⟨y, hy⟩ : K)
      rw [hfpatch i s ⟨hs.1, hsa⟩ hx hxi,
        hfpatch j s ⟨hs.1, hsa⟩ hy hyj] at hxy
      have heq := cylinder_pointMap_eq_on_interval (d i) (d j) ordConnected_Icc
        hxi hyj (s := s) ⟨hs.1, hsa⟩
        (congrArg (fun z => (⟨origin + s / q, z⟩ : F.point)) hxy)
        a ⟨hL.trans ha.le, le_rfl⟩
      rw [hanchor i x hxi, hanchor j y hyj] at heq
      have hsp : e.forward a ⟨ha.le, ha0⟩ x = e.forward a ⟨ha.le, ha0⟩ y :=
        eq_of_heq (Sigma.mk.inj_iff.mp heq).2
      simpa only [e.left_inverse _ _ (hKW hx), e.left_inverse _ _ (hKW hy)] using
        congrArg (e.inverse a ⟨ha.le, ha0⟩) hsp
    · have hso : s ∈ Icc (-T) 0 := ⟨ha.le.trans (le_of_lt (lt_of_not_ge hsa)), hs.2⟩
      rw [hfold s hso hx, hfold s hso hy] at hxy
      simpa only [e.left_inverse _ _ (hKW hx), e.left_inverse _ _ (hKW hy)] using
        congrArg (e.inverse s hso) hxy
  let G : Icc L 0 × K → F.point := fun p => ⟨origin + p.1.1 / q, f p.1.1 p.1.2 p.2.1⟩
  have hGinj : Function.Injective G := by
    rintro ⟨s, x⟩ ⟨t, y⟩ hst
    have hc : s.1 = t.1 := by
      have ht := congrArg Sigma.fst hst
      change origin + s.1 / q = origin + t.1 / q at ht
      exact (div_left_inj' e.scale_pos.ne').mp (add_left_cancel ht)
    have hsub : s = t := Subtype.ext hc
    subst t
    have hsp : f s.1 s.2 x.1 = f s.1 s.2 y.1 :=
      eq_of_heq (Sigma.mk.inj_iff.mp hst).2
    exact Prod.ext rfl (Subtype.ext (hinj s.1 s.2 x.2 y.2 hsp))
  have hGcont : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hpa : p.1.1 < a
    · obtain ⟨i, hpi⟩ := hcover p.2.1 p.2.2
      let O : Set (Icc L 0 × K) := {z | z.1.1 < a ∧ z.2.1 ∈ V i}
      have hO : IsOpen O :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
          ((hV i).preimage (continuous_subtype_val.comp continuous_snd))
      let H : O → Icc L a × V i := fun z =>
        (⟨z.1.1.1, z.1.1.2.1, z.2.1.le⟩, ⟨z.1.2.1, z.2.2⟩)
      have hH : Continuous H :=
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk
          (fun z => ⟨z.1.1.2.1, z.2.1.le⟩)).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk
          (fun z => z.2.2))
      have hcont : Continuous (fun z : O => G z.1) := by
        convert (d i).embedding.continuous.comp hH using 1
        funext z
        exact congrArg (fun w => (⟨origin + z.1.1.1 / q, w⟩ : F.point))
          (hfpatch i z.1.1.1 ⟨z.1.1.2.1, z.2.1.le⟩ z.1.2.2 z.2.2)
      exact (continuousOn_iff_continuous_domRestrict.mpr hcont).continuousAt
        (hO.mem_nhds ⟨hpa, hpi⟩)
    · have hpo : -T < p.1.1 := ha.trans_le (le_of_not_gt hpa)
      let O : Set (Icc L 0 × K) := {z | -T < z.1.1}
      have hO : IsOpen O := isOpen_lt continuous_const
        (continuous_subtype_val.comp continuous_fst)
      let H : O → Icc (-T) 0 × W := fun z =>
        (⟨z.1.1.1, z.2.le, z.1.1.2.2⟩, ⟨z.1.2.1, hKW z.1.2.2⟩)
      have hH : Continuous H :=
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk
          (fun z => ⟨z.2.le, z.1.1.2.2⟩)).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk
          (fun z => hKW z.1.2.2))
      have hcont : Continuous (fun z : O => G z.1) := by
        convert e.embedding.continuous.comp hH using 1
        funext z
        exact congrArg (fun w => (⟨origin + z.1.1.1 / q, w⟩ : F.point))
          (hfold z.1.1.1 ⟨z.2.le, z.1.1.2.2⟩ z.1.2.2)
      exact (continuousOn_iff_continuous_domRestrict.mpr hcont).continuousAt (hO.mem_nhds hpo)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  have : CompactSpace (Icc L 0) := isCompact_iff_compactSpace.mp isCompact_Icc
  have : T2Space F.point := F.space_t2
  have hGemb : Topology.IsEmbedding G := (hGcont.isClosedEmbedding hGinj).isEmbedding
  have hfsmooth (s : ℝ) (hs : s ∈ Icc L 0) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) U := by
    intro x hx
    by_cases hsa : s ≤ a
    · obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
      apply ContMDiffAt.contMDiffWithinAt
      apply ((d i).forward_smooth s ⟨hs.1, hsa⟩).contMDiffAt (hV i |>.mem_nhds hxi)
        |>.congr_of_eventuallyEq
      filter_upwards [(hU.inter (hV i)).mem_nhds ⟨hx, hxi⟩] with y hy
      exact hfpatch i s ⟨hs.1, hsa⟩ (subset_closure hy.1) hy.2
    · have hso : s ∈ Icc (-T) 0 := ⟨ha.le.trans (le_of_lt (lt_of_not_ge hsa)), hs.2⟩
      apply ContMDiffAt.contMDiffWithinAt
      apply (e.forward_smooth s hso).contMDiffAt
        (hW.mem_nhds (hKW (subset_closure hx))) |>.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hfold s hso (subset_closure hy)
  let inv : ∀ s, s ∈ Icc L 0 → (F.slice (origin + s / q)).carrier → C.carrier :=
    fun s hs y => if hy : y ∈ f s hs '' U then Classical.choose hy else x₀
  have hleft (s : ℝ) (hs : s ∈ Icc L 0) : LeftInvOn (inv s hs) (f s hs) U := by
    intro x hx
    have hi : f s hs x ∈ f s hs '' U := mem_image_of_mem _ hx
    simp only [inv, dif_pos hi]
    exact hinj s hs (subset_closure (Classical.choose_spec hi).1) (subset_closure hx)
      (Classical.choose_spec hi).2
  have hright (s : ℝ) (hs : s ∈ Icc L 0) : LeftInvOn (f s hs) (inv s hs) (f s hs '' U) := by
    intro y hy
    simp only [inv, dif_pos hy]
    exact (Classical.choose_spec hy).2
  have hismooth (s : ℝ) (hs : s ∈ Icc L 0) :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inv s hs) (f s hs '' U) := by
    rintro y ⟨x, hx, rfl⟩
    by_cases hsa : s ≤ a
    · obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
      have hfx := hfpatch i s ⟨hs.1, hsa⟩ (subset_closure hx) hxi
      have hopen := cylinder_isOpen_forward_image
        ((d i).restrict Subset.rfl inter_subset_right) (hU.inter (hV i)) s ⟨hs.1, hsa⟩
      change IsOpen ((d i).forward s ⟨hs.1, hsa⟩ '' (U ∩ V i)) at hopen
      have hmem : f s hs x ∈ (d i).forward s ⟨hs.1, hsa⟩ '' (U ∩ V i) :=
        ⟨x, ⟨hx, hxi⟩, hfx.symm⟩
      have hwhole := cylinder_isOpen_forward_image (d i) (hV i) s ⟨hs.1, hsa⟩
      have hwholemem : f s hs x ∈ (d i).forward s ⟨hs.1, hsa⟩ '' V i :=
        ⟨x, hxi, hfx.symm⟩
      apply ContMDiffAt.contMDiffWithinAt
      apply ((d i).inverse_smooth s ⟨hs.1, hsa⟩).contMDiffAt (hwhole.mem_nhds hwholemem)
        |>.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hmem] with z hz
      rcases hz with ⟨w, hw, rfl⟩
      rw [← hfpatch i s ⟨hs.1, hsa⟩ (subset_closure hw.1) hw.2, hleft s hs hw.1]
      rw [hfpatch i s ⟨hs.1, hsa⟩ (subset_closure hw.1) hw.2]
      exact ((d i).left_inverse s ⟨hs.1, hsa⟩ hw.2).symm
    · have hso : s ∈ Icc (-T) 0 := ⟨ha.le.trans (le_of_lt (lt_of_not_ge hsa)), hs.2⟩
      have hUW : U ⊆ W := fun _ hz => hKW (subset_closure hz)
      have hopen := cylinder_isOpen_forward_image (e.restrict Subset.rfl hUW) hU s hso
      change IsOpen (e.forward s hso '' U) at hopen
      have hmem : f s hs x ∈ e.forward s hso '' U := ⟨x, hx, (hfold s hso (subset_closure hx)).symm⟩
      have hwhole := cylinder_isOpen_forward_image e hW s hso
      have hwholemem : f s hs x ∈ e.forward s hso '' W :=
        ⟨x, hUW hx, (hfold s hso (subset_closure hx)).symm⟩
      apply ContMDiffAt.contMDiffWithinAt
      apply (e.inverse_smooth s hso).contMDiffAt (hwhole.mem_nhds hwholemem)
        |>.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hmem] with z hz
      rcases hz with ⟨w, hw, rfl⟩
      rw [← hfold s hso (subset_closure hw), hleft s hs hw]
      rw [hfold s hso (subset_closure hw)]
      exact (e.left_inverse s hso (hUW hw)).symm
  have hvert (s : ℝ) (hs : s ∈ Icc L 0) (x : C.carrier) (hx : x ∈ U) :
      ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ delta : ℝ, 0 < delta ∧
        ∀ s' (hs' : s' ∈ Icc L 0), |s' - s| < delta →
          ∃ hb : origin + s' / q ∈ (F.box b).interval,
            f s' hs' x = (F.box b).forward (origin + s' / q) hb y := by
    by_cases hsa : s < a
    · obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
      obtain ⟨b, y, delta, hdelta, hv⟩ := (d i).vertical_compatibility s ⟨hs.1, hsa.le⟩ x hxi
      refine ⟨b, y, min delta (a - s), lt_min hdelta (sub_pos.mpr hsa), ?_⟩
      intro s' hs' hnear
      have hna := (lt_min_iff.mp hnear).2
      have hsa' : s' ≤ a := by have := (abs_lt.mp hna).2; linarith
      obtain ⟨hb, hbval⟩ := hv s' ⟨hs'.1, hsa'⟩ ((lt_min_iff.mp hnear).1)
      exact ⟨hb, (hfpatch i s' ⟨hs'.1, hsa'⟩ (subset_closure hx) hxi).trans hbval⟩
    · have hso : -T < s := ha.trans_le (le_of_not_gt hsa)
      obtain ⟨b, y, delta, hdelta, hv⟩ := e.vertical_compatibility s ⟨hso.le, hs.2⟩ x
        (hKW (subset_closure hx))
      refine ⟨b, y, min delta (s + T), lt_min hdelta (by linarith), ?_⟩
      intro s' hs' hnear
      have hna := (lt_min_iff.mp hnear).2
      have hso' : -T ≤ s' := by have := (abs_lt.mp hna).1; linarith
      obtain ⟨hb, hbval⟩ := hv s' ⟨hso', hs'.2⟩ ((lt_min_iff.mp hnear).1)
      exact ⟨hb, (hfold s' ⟨hso', hs'.2⟩ (subset_closure hx)).trans hbval⟩
  let g : GeneralizedFlowCylinder F C origin q (Icc L 0) U := {
    scale_pos := e.scale_pos
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
  · intro s hs x hx
    exact congrArg (fun z => (⟨origin + s / q, z⟩ : F.point))
      (hfold s hs (subset_closure hx))
  · intro s hs hsa x hx
    obtain ⟨i, hxi⟩ := hcover x (subset_closure hx)
    exact ⟨i, hxi, congrArg (fun z => (⟨origin + s / q, z⟩ : F.point))
      (hfpatch i s ⟨hs.1, hsa⟩ (subset_closure hx) hxi)⟩





theorem exists_cylinder_backward_extension_of_strongNecks
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilonStar K : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧ 0 < K ∧
      ∀ {M B c : ℝ}, 0 < M → 0 ≤ B → K * M ≤ B →
        0 < c → c ≤ 1 / (4 * M) →
      ∀ {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
        {origin q T a : ℝ} {U W : Set C.carrier},
      ∀ (e : GeneralizedFlowCylinder F C origin q (Icc (-T) 0) W),
        IsOpen U → IsOpen W → U.Nonempty → IsCompact (closure U) → closure U ⊆ W →
      ∀ (hTc : c ≤ T) (ha : -T < a) (hac : a ≤ -T + c),
        (∀ s hs x, x ∈ W → F.scalar (e.pointMap s hs x) ≤ M * q) →
        (∀ s hs x, x ∈ W → |F.curvatureNorm (e.pointMap s hs x)| ≤ B * q) →
        (∀ x ∈ closure U, ∃ epsilon, epsilon ≤ epsilonStar ∧
          ∃ N : GeneralizedStrongNeck F (origin + a / q) epsilon,
            N.center = e.forward a ⟨ha.le, by linarith⟩ x) →
        ∃ g : GeneralizedFlowCylinder F C origin q (Icc (-(T + c)) 0) U,
          (∀ s (hs : s ∈ Icc (-T) 0) x, x ∈ U →
            g.pointMap s ⟨by linarith [hs.1], hs.2⟩ x = e.pointMap s hs x) ∧
          (∀ s hs x, x ∈ U → F.scalar (g.pointMap s hs x) ≤ M * q) ∧
          (∀ s hs x, x ∈ U → |F.curvatureNorm (g.pointMap s hs x)| ≤ B * q) := by
  obtain ⟨epsilonR, K, hRpos, hRsmall, hK, hcurvature⟩ :=
    exists_strongNeck_backward_curvature_bound.{u}
  obtain ⟨epsilonS, hSpos, _hSsmall, hscalarNeck⟩ :=
    exists_strongNeck_backward_scalarDerivative_comparison hM04
  refine ⟨min epsilonR epsilonS, K, lt_min hRpos hSpos,
    (min_le_left _ _).trans hRsmall, hK, ?_⟩
  intro M B c hM _hB hKM hc hcM F C origin q T a U W e hU hW hne hcompact hKW
    hTc ha hac hscalar hcurv hneck
  have ha0 : a ≤ 0 := by linarith
  have haOld : a ∈ Icc (-T) 0 := ⟨ha.le, ha0⟩
  choose epsilon hepsilon N hcenter using fun x : closure U => hneck x.1 x.2
  let V : closure U → Set C.carrier := fun i => W ∩ (e.forward a haOld) ⁻¹' (N i).carrier
  have hV (i : closure U) : IsOpen (V i) :=
    (e.forward_smooth a haOld).continuousOn.isOpen_inter_preimage hW (N i).carrier_open
  have hcover : ∀ x ∈ closure U, ∃ i, x ∈ V i := by
    intro x hx
    refine ⟨⟨x, hx⟩, hKW hx, ?_⟩
    change e.forward a haOld x ∈ (N ⟨x, hx⟩).carrier
    rw [← hcenter ⟨x, hx⟩]
    exact (N ⟨x, hx⟩).central_sphere_subset (N ⟨x, hx⟩).center_on_central_sphere
  have hRbound (i : closure U) : (N i).scale⁻¹ ^ 2 ≤ M * q := by
    have hscale : (N i).scale =
        (Real.sqrt ((F.connection (origin + a / q)).scalarCurvature (N i).center))⁻¹ := by
      rw [(N i).scale_scalar, neg_div, Real.rpow_neg (N i).scalar_center_pos.le,
        Real.sqrt_eq_rpow]
    rw [hscale, inv_inv, Real.sq_sqrt (N i).scalar_center_pos.le, hcenter i]
    exact hscalar a haOld i.1 (hKW i.2)
  have hnative (i : closure U) : ∀ s ∈ Icc (-(T + c)) a,
      (s - a) * ((N i).scale⁻¹ ^ 2) / q ∈ Ioc (-1) 0 := by
    intro s hs
    have hRi : 0 < (N i).scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr (N i).scale_pos)
    have hcmul : c * (4 * M) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4 * M)).mp hcM
    have hslope : (a - s) * ((N i).scale⁻¹ ^ 2) ≤ 2 * c * (M * q) := by
      calc
        (a - s) * ((N i).scale⁻¹ ^ 2) ≤ (2 * c) * ((N i).scale⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith [hs.1]) hRi.le
        _ ≤ 2 * c * (M * q) := mul_le_mul_of_nonneg_left (hRbound i) (by positivity)
    have hhalf : 2 * c * (M * q) ≤ q / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hcmul e.scale_pos.le]
    refine ⟨(lt_div_iff₀ e.scale_pos).mpr ?_,
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2)
        hRi.le) e.scale_pos.le⟩
    nlinarith [hslope.trans hhalf, e.scale_pos]
  let d (i : closure U) : GeneralizedFlowCylinder F C origin q
      (Icc (-(T + c)) a) (V i) :=
    strongNeckAttachedCylinder e hW haOld (N i) (hnative i)
  have hanchor (i : closure U) (x : C.carrier) (hx : x ∈ V i) :
      (d i).pointMap a ⟨by linarith, le_rfl⟩ x = e.pointMap a haOld x := by
    rw [strongNeckAttachedCylinder_pointMap]
    have hid (r : ℝ) (hr : r ∈ Ioc (-1) 0) (hr0 : r = 0) :
        (N i).time_cylinder.pointMap r hr (e.forward a haOld x) = e.pointMap a haOld x := by
      subst r
      change (N i).time_cylinder.pointMap 0 hr (e.forward a haOld x) =
        (⟨origin + a / q, e.forward a haOld x⟩ : F.point)
      exact (N i).cylinder_identity hr (e.forward a haOld x) hx.2
    exact hid _ _ (by ring)
  obtain ⟨g, hgold, hgpatch⟩ := glue_cylinders_on_compact_source e hU hW hne hcompact hKW
    (by linarith : -(T + c) ≤ -T) ha ha0 V d hV hcover hanchor
  refine ⟨g, hgold, ?_, ?_⟩
  · intro s hs x hx
    by_cases hsa : s ≤ a
    · obtain ⟨i, hxi, hpoint⟩ := hgpatch s hs hsa x hx
      rw [hpoint, strongNeckAttachedCylinder_pointMap]
      exact ((hscalarNeck (N i) ((hepsilon i).trans (min_le_right _ _))
        (e.forward a haOld x) hxi.2).2.2 _ (hnative i s ⟨hs.1, hsa⟩)).trans
        (hscalar a haOld x hxi.1)
    · have hso : s ∈ Icc (-T) 0 := ⟨ha.le.trans (le_of_lt (lt_of_not_ge hsa)), hs.2⟩
      rw [hgold s hso x hx]
      exact hscalar s hso x (hKW (subset_closure hx))
  · intro s hs x hx
    by_cases hsa : s ≤ a
    · obtain ⟨i, hxi, hpoint⟩ := hgpatch s hs hsa x hx
      rw [hpoint, strongNeckAttachedCylinder_pointMap]
      calc
        _ ≤ K * ((N i).scale⁻¹ ^ 2) :=
          hcurvature (N i) ((hepsilon i).trans (min_le_left _ _))
            (hnative i s ⟨hs.1, hsa⟩) (e.forward a haOld x) hxi.2
        _ ≤ K * (M * q) := mul_le_mul_of_nonneg_left (hRbound i) hK.le
        _ = (K * M) * q := (mul_assoc _ _ _).symm
        _ ≤ B * q := mul_le_mul_of_nonneg_right hKM e.scale_pos.le
    · have hso : s ∈ Icc (-T) 0 := ⟨ha.le.trans (le_of_lt (lt_of_not_ge hsa)), hs.2⟩
      rw [hgold s hso x hx]
      exact hcurv s hso x (hKW (subset_closure hx))

end PoincareConjecture.M32
