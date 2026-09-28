import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.BoundaryLineStraightening
import PoincareConjecture.Proofs.M76.Wall.InteriorArcPairChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76


theorem PLDomain.exists_boundary_interior_arc_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) {f : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hi : InjOn f (Icc (0 : ℝ) 1))
    (hfr : f '' Icc (0 : ℝ) 1 ⊆ frontier R)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {W : Set X} (hW : IsOpen W) (hxW : f a ∈ W) :
    ∃ (T : OpenPartialHomeomorph X (Fin 3 → ℝ))
      (ell psi : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (b c : Fin 3 → ℝ),
      f a ∈ T.source ∧ T.source ⊆ W ∧ T (f a) = 0 ∧
      (∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      ell.contLinear b = 0 ∧ psi.contLinear b = 1 ∧
      ell.contLinear c = 1 ∧ psi.contLinear c = 0 ∧
      (∀ y ∈ T.source,y ∈ frontier R ↔ ell (T y) = 0) ∧
      ∀ y ∈ T.source,y ∈ f '' Icc (0 : ℝ) 1 ↔
        ell (T y) = 0 ∧ psi (T y) = 0 := by
  obtain ⟨B,A,hxB,hzero,hA,hBcompat,_,hfront⟩ :=
    he.exists_centered_boundary_chart (hfr ⟨a,⟨ha.1.le,ha.2.le⟩,rfl⟩)
  obtain ⟨u,v,hu,hv,hne,δm,hδm,δp,hδp,hmapm,hmapp,hformm,hformp⟩ :=
    hf.exists_interior_chart_vectors hi ha B hBcompat hxB hzero
  let fm : ℝ → X := fun t => f (a - a * t)
  let fp : ℝ → X := fun t => f (a + (1 - a) * t)
  have ham : MapsTo (fun t : ℝ => a - a * t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1, ha.2]
  have hap : MapsTo (fun t : ℝ => a + (1 - a) * t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1, ha.2]
  have hcm : ContinuousOn fm (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn ham
  have hcp : ContinuousOn fp (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hap
  have him : InjOn fm (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hi (ham hs) (ham ht) hst
    exact (mul_left_cancel₀ ha.1.ne') (by linarith)
  have hip : InjOn fp (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hi (hap hs) (hap ht) hst
    exact (mul_left_cancel₀ (sub_pos.mpr ha.2).ne') (by linarith)
  have hm0 : fm 0 = f a := by simp [fm]
  have hp0 : fp 0 = f a := by simp [fp]
  obtain ⟨Um, hUm, hxm, hUmW, hraym⟩ := B.exists_endpoint_arc_neighborhood hcm him
    (by simpa only [hm0] using hxB) (by simpa only [hm0] using hzero)
    hδm.1 hδm.2.le hu hmapm hformm hW (by simpa only [hm0] using hxW)
  obtain ⟨Up, hUp, hxp, _, hrayp⟩ := B.exists_endpoint_arc_neighborhood hcp hip
    (by simpa only [hp0] using hxB) (by simpa only [hp0] using hzero)
    hδp.1 hδp.2.le hv hmapp hformp hW (by simpa only [hp0] using hxW)
  have hsplit : f '' Icc (0 : ℝ) 1 = fm '' Icc 0 1 ∪ fp '' Icc 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, hft⟩
      by_cases hta : t ≤ a
      · have hs : (a - t) / a ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (sub_nonneg.mpr hta) ha.1.le,
            (div_le_iff₀ ha.1).mpr (by nlinarith [ht.1])⟩
        refine Or.inl ⟨(a - t) / a, hs, ?_⟩
        change f (a - a * ((a - t) / a)) = y
        rw [mul_div_cancel₀ _ ha.1.ne', sub_sub_cancel]
        exact hft
      · have hpos : 0 < 1 - a := sub_pos.mpr ha.2
        have hs : (t - a) / (1 - a) ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (by linarith) hpos.le,
            (div_le_iff₀ hpos).mpr (by nlinarith [ht.2])⟩
        refine Or.inr ⟨(t - a) / (1 - a), hs, ?_⟩
        change f (a + (1 - a) * ((t - a) / (1 - a))) = y
        rw [mul_div_cancel₀ _ hpos.ne', show a + (t - a) = t by ring]
        exact hft
    · rintro (⟨t, ht, hft⟩ | ⟨t, ht, hft⟩)
      · exact ⟨a - a * t, ham ht, hft⟩
      · exact ⟨a + (1 - a) * t, hap ht, hft⟩

  have hAu : A u = 0 := by
    have hz := (hfront _ (hmapm ⟨hδm.1.le,le_rfl⟩)).mp
      (hfr ⟨a-a*δm,ham ⟨hδm.1.le,hδm.2.le⟩,rfl⟩)
    rw [hformm _ ⟨hδm.1.le,le_rfl⟩,map_smul,smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hδm.1.ne'
  have hAv : A v = 0 := by
    have hz := (hfront _ (hmapp ⟨hδp.1.le,le_rfl⟩)).mp
      (hfr ⟨a+(1-a)*δp,hap ⟨hδp.1.le,hδp.2.le⟩,rfl⟩)
    rw [hformp _ ⟨hδp.1.le,le_rfl⟩,map_smul,smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hδp.1.ne'
  obtain ⟨T,ell,psi,b,c,hxT,hTs,hT0,hTc,hb,hpb,hc,hpc,hTF,hTL⟩ :=
    exists_compatible_plane_rim_chart_of_rays e B hBcompat A hA (L := f '' Icc 0 1) hxB hzero hfront
      (hUm.inter hUp) ⟨by simpa only [hm0] using hxm,by simpa only [hp0] using hxp⟩
      hu hv hne hAu hAv (fun y hy => by
        rw [hsplit,mem_union,hraym y hy.1,hrayp y hy.2])
  exact ⟨T,ell,psi,b,c,hxT,fun y hy => (hUmW (hTs hy).1).2,
    hT0,hTc,hb,hpb,hc,hpc,hTF,hTL⟩


theorem PLDomain.exists_boundary_two_arc_endpoint_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) {f g : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hg : PolyhedralPLInCharts e g (Icc (0 : ℝ) 1))
    (hfi : InjOn f (Icc (0 : ℝ) 1)) (hgi : InjOn g (Icc (0 : ℝ) 1))
    (hfr : f '' Icc (0 : ℝ) 1 ⊆ frontier R)
    (hgr : g '' Icc (0 : ℝ) 1 ⊆ frontier R)
    (h0 : f 0 = g 0)
    (hinter : f '' Icc (0 : ℝ) 1 ∩ g '' Icc (0 : ℝ) 1 ⊆ {f 0,f 1})
    {W : Set X} (hW : IsOpen W) (hxW : f 0 ∈ W) :
    ∃ (T : OpenPartialHomeomorph X (Fin 3 → ℝ))
      (ell psi : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (a b : Fin 3 → ℝ),
      f 0 ∈ T.source ∧ T.source ⊆ W ∧ T (f 0) = 0 ∧
      (∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      ell.contLinear a = 0 ∧ psi.contLinear a = 1 ∧
      ell.contLinear b = 1 ∧ psi.contLinear b = 0 ∧
      (∀ y ∈ T.source,y ∈ frontier R ↔ ell (T y) = 0) ∧
      ∀ y ∈ T.source,y ∈ f '' Icc (0 : ℝ) 1 ∪ g '' Icc (0 : ℝ) 1 ↔
        ell (T y) = 0 ∧ psi (T y) = 0 := by
  obtain ⟨B,A,hxB,hzero,hA,hBc,_,hfront⟩ :=
    he.exists_centered_boundary_chart (hfr ⟨0,⟨le_rfl,zero_le_one⟩,rfl⟩)
  obtain ⟨u,hu,δm,hδm,hmapm,hformm⟩ :=
    hf.exists_initial_chart_vector hfi B hBc hxB hzero
  obtain ⟨v,hv,δp,hδp,hmapp,hformp⟩ :=
    hg.exists_initial_chart_vector hgi B hBc (h0 ▸ hxB) (h0 ▸ hzero)
  have hAu : A u = 0 := by
    have hz := (hfront _ (hmapm ⟨hδm.1.le,le_rfl⟩)).mp
      (hfr ⟨δm,⟨hδm.1.le,hδm.2.le⟩,rfl⟩)
    rw [hformm _ ⟨hδm.1.le,le_rfl⟩,map_smul,smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hδm.1.ne'
  have hAv : A v = 0 := by
    have hz := (hfront _ (hmapp ⟨hδp.1.le,le_rfl⟩)).mp
      (hgr ⟨δp,⟨hδp.1.le,hδp.2.le⟩,rfl⟩)
    rw [hformp _ ⟨hδp.1.le,le_rfl⟩,map_smul,smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hδp.1.ne'
  have hne : ∀ c : ℝ,0 < c → u ≠ c • v := by
    intro c hc huv
    let s : ℝ := min (δm / 2) (δp / (2 * c))
    have hs : 0 < s := lt_min (by linarith [hδm.1])
      (div_pos hδp.1 (mul_pos zero_lt_two hc))
    have hsm : s ≤ δm := (min_le_left _ _).trans (by linarith [hδm.1])
    have hsp : c * s ≤ δp := by
      have hbound := (le_div_iff₀ (mul_pos zero_lt_two hc)).mp
        (show s ≤ δp / (2*c) from min_le_right _ _)
      nlinarith [mul_pos hc hs]
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.le,hsm.trans hδm.2.le⟩
    have hcsI : c*s ∈ Icc (0 : ℝ) 1 := ⟨(mul_pos hc hs).le,hsp.trans hδp.2.le⟩
    have hfg : f s = g (c*s) := B.injOn (hmapm ⟨hs.le,hsm⟩)
      (hmapp ⟨(mul_pos hc hs).le,hsp⟩) (by
        rw [hformm _ ⟨hs.le,hsm⟩,hformp _ ⟨(mul_pos hc hs).le,hsp⟩,
          huv,smul_smul,mul_comm s c])
    have hm := hinter ⟨⟨s,hsI,rfl⟩,⟨c*s,hcsI,hfg.symm⟩⟩
    rcases mem_insert_iff.mp hm with hm | hm
    · exact hs.ne' (hfi hsI ⟨le_rfl,zero_le_one⟩ hm)
    · have hs1 := hfi hsI ⟨zero_le_one,le_rfl⟩ (mem_singleton_iff.mp hm)
      linarith [hδm.2]
  obtain ⟨Um,hUm,hxm,hUmW,hraym⟩ := B.exists_endpoint_arc_neighborhood
    hf.continuousOn hfi hxB hzero hδm.1 hδm.2.le hu hmapm hformm hW hxW
  obtain ⟨Up,hUp,hxp,_,hrayp⟩ := B.exists_endpoint_arc_neighborhood
    hg.continuousOn hgi (h0 ▸ hxB) (h0 ▸ hzero) hδp.1 hδp.2.le hv hmapp hformp
    hW (h0 ▸ hxW)
  obtain ⟨T,ell,psi,a,b,hxT,hTs,hT0,hTc,ha,hpa,hb,hpb,hTF,hTL⟩ :=
    exists_compatible_plane_rim_chart_of_rays e B hBc A hA
      (L := f '' Icc 0 1 ∪ g '' Icc 0 1) hxB hzero hfront
      (hUm.inter hUp) ⟨hxm,h0.symm ▸ hxp⟩ hu hv hne hAu hAv
      (fun y hy => by rw [mem_union,hraym y hy.1,hrayp y hy.2])
  exact ⟨T,ell,psi,a,b,hxT,fun y hy => (hUmW (hTs hy).1).2,
    hT0,hTc,ha,hpa,hb,hpb,hTF,hTL⟩


theorem PLDomain.exists_boundary_two_arc_chart_at_first
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) {f g : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hg : PolyhedralPLInCharts e g (Icc (0 : ℝ) 1))
    (hfi : InjOn f (Icc (0 : ℝ) 1)) (hgi : InjOn g (Icc (0 : ℝ) 1))
    (hfr : f '' Icc (0 : ℝ) 1 ⊆ frontier R)
    (hgr : g '' Icc (0 : ℝ) 1 ⊆ frontier R)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hinter : f '' Icc (0 : ℝ) 1 ∩ g '' Icc (0 : ℝ) 1 ⊆ {f 0,f 1})
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {W : Set X} (hW : IsOpen W) (hxW : f t ∈ W) :
    ∃ (T : OpenPartialHomeomorph X (Fin 3 → ℝ))
      (ell psi : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (a b : Fin 3 → ℝ),
      f t ∈ T.source ∧ T.source ⊆ W ∧ T (f t) = 0 ∧
      (∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      ell.contLinear a = 0 ∧ psi.contLinear a = 1 ∧
      ell.contLinear b = 1 ∧ psi.contLinear b = 0 ∧
      (∀ y ∈ T.source,y ∈ frontier R ↔ ell (T y) = 0) ∧
      ∀ y ∈ T.source,y ∈ f '' Icc (0 : ℝ) 1 ∪ g '' Icc (0 : ℝ) 1 ↔
        ell (T y) = 0 ∧ psi (T y) = 0 := by
  by_cases ht0 : t = 0
  · subst t
    exact he.exists_boundary_two_arc_endpoint_chart hf hg hfi hgi hfr hgr h0 hinter hW hxW
  by_cases ht1 : t = 1
  · subst t
    let r : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ
    have hr (x : ℝ) : r x = 1-x := rfl
    have hrI : r '' Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        change 0 ≤ 1-y ∧ 1-y ≤ 1
        constructor <;> linarith [hy.1,hy.2]
      · intro hx
        exact ⟨1-x,⟨by linarith [hx.2],by linarith [hx.1]⟩,by simp [hr]⟩
    have hrmap : MapsTo r (Icc (0 : ℝ) 1) (Icc 0 1) := fun x hx => hrI.subset ⟨x,hx,rfl⟩
    have hri : Function.Injective r := by intro x y h; change 1-x=1-y at h; linarith
    have himage (q : ℝ → X) : (q ∘ r) '' Icc (0 : ℝ) 1 = q '' Icc 0 1 := by
      rw [image_comp,hrI]
    have hPL (q : ℝ → X) (hq : PolyhedralPLInCharts e q (Icc (0 : ℝ) 1)) :
        PolyhedralPLInCharts e (q ∘ r) (Icc (0 : ℝ) 1) := by
      obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := isFinitePLBallPair_Icc zero_lt_one
      rw [←hKs]
      exact hq.comp_finitePiecewiseAffineOn K hK
        ((K.affineOnFaces_affine r).finitePiecewiseAffineOn hK)
        (fun x hx => hrmap (hKs.subset hx))
    have hrev := he.exists_boundary_two_arc_endpoint_chart (hPL f hf) (hPL g hg)
      (hfi.comp hri.injOn hrmap) (hgi.comp hri.injOn hrmap)
      (by rwa [himage]) (by rwa [himage]) (by simpa [Function.comp_def,hr] using h1)
      (by rw [himage f,himage g]; simpa only [Function.comp_apply,hr,sub_zero,sub_self,pair_comm] using hinter)
      hW (by simpa [Function.comp_def,hr] using hxW)
    rw [himage f,himage g] at hrev
    simpa only [Function.comp_apply,hr,sub_zero] using hrev
  have htg : f t ∉ g '' Icc (0 : ℝ) 1 := by
    intro h
    rcases mem_insert_iff.mp (hinter ⟨⟨t,ht,rfl⟩,h⟩) with h | h
    · exact ht0 (hfi ht ⟨le_rfl,zero_le_one⟩ h)
    · exact ht1 (hfi ht ⟨zero_le_one,le_rfl⟩ (mem_singleton_iff.mp h))
  have hc : IsClosed (g '' Icc (0 : ℝ) 1) := (isCompact_Icc.image_of_continuousOn hg.continuousOn).isClosed
  obtain ⟨T,ell,psi,a,b,hxT,hTs,hT0,hTc,ha,hpa,hb,hpb,hTF,hTL⟩ :=
    he.exists_boundary_interior_arc_chart hf hfi hfr
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),lt_of_le_of_ne ht.2 ht1⟩
      (hW.inter hc.isOpen_compl) ⟨hxW,htg⟩
  refine ⟨T,ell,psi,a,b,hxT,fun y hy => (hTs hy).1,hT0,hTc,ha,hpa,hb,hpb,hTF,?_⟩
  intro y hy
  rw [mem_union,or_iff_left (hTs hy).2]
  exact hTL y hy


theorem exists_original_interval_parameter
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {U : Set E} {a b : E} (hU : IsFinitePLBallPair ℝ U {a,b}) (hab : a ≠ b)
    {f : E → X} (hf : PolyhedralPLInCharts e f U) (hfi : InjOn f U) :
    ∃ F : ℝ → X, PolyhedralPLInCharts e F (Icc (0 : ℝ) 1) ∧
      InjOn F (Icc (0 : ℝ) 1) ∧ F '' Icc (0 : ℝ) 1 = f '' U ∧
      F 0 = f a ∧ F 1 = f b := by
  obtain ⟨p,⟨q,hq,hpq⟩,hp0,hp1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  have hqU : q '' Icc (0 : ℝ) 1 = U := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      rw [←hpq ⟨t,ht⟩]
      exact (p ⟨t,ht⟩).property
    · intro hy
      exact ⟨p.symm ⟨y,hy⟩,(p.symm ⟨y,hy⟩).property,
        (hpq _).symm.trans (congrArg Subtype.val (p.apply_symm_apply ⟨y,hy⟩))⟩
  have hmap : MapsTo q (Icc (0 : ℝ) 1) U := fun x hx => hqU.subset ⟨x,hx,rfl⟩
  have hqi : InjOn q (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hp : p ⟨x,hx⟩ = p ⟨y,hy⟩ := Subtype.ext (by simpa only [hpq] using hxy)
    exact congrArg Subtype.val (p.injective hp)
  refine ⟨f ∘ q,?_,hfi.comp hqi hmap,by rw [image_comp,hqU],?_,?_⟩
  · obtain ⟨K,hK,hKs,hqa⟩ := hq
    rw [←hKs]
    exact hf.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hqa⟩
      (fun x hx => hmap (hKs.subset hx))
  · change f (q 0) = f a
    rw [←hpq ⟨0,⟨le_rfl,zero_le_one⟩⟩,hp0]
  · change f (q 1) = f b
    rw [←hpq ⟨1,⟨zero_le_one,le_rfl⟩⟩,hp1]




theorem PLDomain.exists_boundary_two_interval_loop_chart
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) {U : Set E} {V : Set F} {a b : E} {c d : F}
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hV : IsFinitePLBallPair ℝ V {c,d})
    (hab : a ≠ b) (hcd : c ≠ d)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f U) (hg : PolyhedralPLInCharts e g V)
    (hfi : InjOn f U) (hgi : InjOn g V)
    (h0 : f a = g c) (h1 : f b = g d)
    (hinter : f '' U ∩ g '' V = {f a,f b})
    (hfront : f '' U ∪ g '' V ⊆ frontier R)
    {x : X} (hx : x ∈ f '' U ∪ g '' V)
    {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ (T : OpenPartialHomeomorph X (Fin 3 → ℝ))
      (ell psi : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (u v : Fin 3 → ℝ),
      x ∈ T.source ∧ T.source ⊆ W ∧ T x = 0 ∧
      (∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      ell.contLinear u = 0 ∧ psi.contLinear u = 1 ∧
      ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
      (∀ y ∈ T.source,y ∈ frontier R ↔ ell (T y) = 0) ∧
      ∀ y ∈ T.source,y ∈ f '' U ∪ g '' V ↔ ell (T y) = 0 ∧ psi (T y) = 0 := by
  obtain ⟨p,hp,hpi,hpI,hp0,hp1⟩ := exists_original_interval_parameter hU hab hf hfi
  obtain ⟨q,hq,hqi,hqI,hq0,hq1⟩ := exists_original_interval_parameter hV hcd hg hgi
  have hpR : p '' Icc (0 : ℝ) 1 ⊆ frontier R := by
    rw [hpI]
    exact subset_union_left.trans hfront
  have hqR : q '' Icc (0 : ℝ) 1 ⊆ frontier R := by
    rw [hqI]
    exact subset_union_right.trans hfront
  have hpq0 : p 0 = q 0 := by rw [hp0,hq0,h0]
  have hpq1 : p 1 = q 1 := by rw [hp1,hq1,h1]
  have hpq : p '' Icc (0 : ℝ) 1 ∩ q '' Icc (0 : ℝ) 1 ⊆ {p 0,p 1} := by
    rw [hpI,hqI,hinter,hp0,hp1]
  rw [←hpI,←hqI] at hx
  rcases hx with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
  · have h := he.exists_boundary_two_arc_chart_at_first hp hq hpi hqi hpR hqR
      hpq0 hpq1 hpq ht hW hxW
    simpa only [hpI,hqI] using h
  · have hqp : q '' Icc (0 : ℝ) 1 ∩ p '' Icc (0 : ℝ) 1 ⊆ {q 0,q 1} := by
      simpa only [inter_comm,hpq0,hpq1] using hpq
    have h := he.exists_boundary_two_arc_chart_at_first hq hp hqi hpi hqR hpR
      hpq0.symm hpq1.symm hqp ht hW hxW
    simpa only [hpI,hqI,union_comm] using h

end PoincareConjecture.M76

