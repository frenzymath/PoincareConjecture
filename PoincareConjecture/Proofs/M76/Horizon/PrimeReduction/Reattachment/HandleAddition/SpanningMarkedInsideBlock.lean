import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningBigonCornerDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Product
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.exists_marked_bigon_inside_block
    {X α F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : α → OpenPartialHomeomorph X V3} {N E S O : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j)
    (hNfront : frontier N = N ∩ (frontier E ∪ S))
    (hPO : MapsTo P.map (Disk ×ˢ I) O)
    {d U C : Set F} (hd : IsFinitePLBallPair P2 d (U ∪ C))
    (H : Disk ≃ₜ d) (hH : H.IsFinitePL)
    (hHrim : ∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : F) ∈ U ∪ C)
    {f : F → X} (hj : ∀ z : Disk, j z = f (H z))
    (hjU : ∀ z : Disk, j z ∈ frontier E ↔ (H z : F) ∈ U)
    (hjC : ∀ z : Disk, j z ∈ S ↔ (H z : F) ∈ C)
    (hmark : ∀ z ∈ Rim, ∀ t ∈ I,
      (P.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
      (P.map (z,t) ∈ S ↔ j z ∈ S)) :
    ∃ k : F × ℝ → X,
      PolyhedralPLInCharts e k (d ×ˢ I) ∧ InjOn k (d ×ˢ I) ∧
      (∀ z (hz : z ∈ d ×ˢ I), k z = P.map (H.symm ⟨z.1,hz.1⟩,z.2)) ∧
      (∀ x ∈ d,k (x,0) = f x) ∧ MapsTo k (d ×ˢ I) (N ∩ O) ∧
      Nonempty (ChartwisePLBall e (k '' (d ×ˢ I))
        (k '' (((U ∪ C) ×ˢ I) ∪ (d ×ˢ ({-1,1} : Set ℝ))))) ∧
      (∀ z ∈ d ×ˢ I,k z ∈ frontier E ↔ z.1 ∈ U) ∧
      (∀ z ∈ d ×ˢ I,k z ∈ S ↔ z.1 ∈ C) ∧
      k '' (d ×ˢ I) ∩ frontier E = k '' (U ×ˢ I) ∧
      k '' (d ×ˢ I) ∩ S = k '' (C ×ˢ I) ∧
      k '' (U ×ˢ I) ∩ S = k '' ((U ∩ C) ×ˢ I) ∧
      (k '' (((U ∪ C) ×ˢ I) ∪ (d ×ˢ ({-1,1} : Set ℝ)))) ∩ frontier E =
        k '' (U ×ˢ I) ∧
      ((k '' (((U ∪ C) ×ˢ I) ∪ (d ×ˢ ({-1,1} : Set ℝ)))) \ k '' (U ×ˢ I)).Nonempty := by
  obtain ⟨r,hr,hrval⟩ := hH.symm
  have hrmap : MapsTo r d Disk := by
    intro x hx
    rw [←hrval ⟨x,hx⟩]
    exact (H.symm ⟨x,hx⟩).property
  have hrinj : InjOn r d := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.symm.injective (Subtype.ext
      ((hrval ⟨x,hx⟩).trans (hxy.trans (hrval ⟨y,hy⟩).symm))))
  have hHr (x : F) (hx : x ∈ d) : (H ⟨r x,hrmap hx⟩ : F) = x := by
    have hh : (⟨r x,hrmap hx⟩ : Disk) = H.symm ⟨x,hx⟩ := Subtype.ext (hrval ⟨x,hx⟩).symm
    rw [hh,H.apply_symm_apply]
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJI,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    ⟨J,hJ,hJI,J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let G := Prod.map r (id : ℝ → ℝ)
  have hG : FinitePiecewiseAffineOn G (d ×ˢ I) := hr.prodMap hid
  have hGmap : MapsTo G (d ×ˢ I) (Disk ×ˢ I) := fun z hz => ⟨hrmap hz.1,hz.2⟩
  let k := P.map ∘ G
  have hk : PolyhedralPLInCharts e k (d ×ˢ I) := by
    obtain ⟨K,hK,hKs,hKf⟩ := hG
    rw [←hKs]
    exact P.polyhedral.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hKf⟩
      (fun z hz => hGmap (hKs.subset hz))
  have hki : InjOn k (d ×ˢ I) := by
    intro z hz w hw hzw
    have hh := P.injective (hGmap hz) (hGmap hw) hzw
    exact Prod.ext (hrinj hz.1 hw.1 (congrArg Prod.fst hh))
      (show z.2 = w.2 from congrArg (fun z : V2 × ℝ => z.2) hh)
  have hmark' {T : Set X} {A : Set F} (hT : T ⊆ frontier E ∪ S)
      (hA : A ⊆ U ∪ C) (hjT : ∀ z : Disk,j z ∈ T ↔ (H z : F) ∈ A)
      (hPT : ∀ z ∈ Rim,∀ t ∈ I,P.map (z,t) ∈ T ↔ j z ∈ T)
      (z : F × ℝ) (hz : z ∈ d ×ˢ I) : k z ∈ T ↔ z.1 ∈ A := by
    have heq := hHr z.1 hz.1
    constructor
    · intro hmem
      have hfr : P.map (G z) ∈ frontier N := hNfront.symm.subset
        ⟨P.inside (hGmap hz),hT hmem⟩
      have hrim := (P.proper (G z) (hGmap hz)).mp hfr
      have hcen := (hPT (r z.1) hrim z.2 hz.2).mp hmem
      exact heq ▸ (hjT ⟨r z.1,hrmap hz.1⟩).mp hcen
    · intro hmem
      have hcenter : j (r z.1) ∈ T := (hjT ⟨r z.1,hrmap hz.1⟩).mpr (heq.symm ▸ hmem)
      have hrim : r z.1 ∈ Rim := (hHrim ⟨r z.1,hrmap hz.1⟩).mpr (heq.symm ▸ hA hmem)
      exact (hPT (r z.1) hrim z.2 hz.2).mpr hcenter
  have hkU := hmark' subset_union_left subset_union_left hjU
    (fun z hz t ht => (hmark z hz t ht).1)
  have hkC := hmark' subset_union_right subset_union_right hjC
    (fun z hz t ht => (hmark z hz t ht).2)
  have hUA : U ⊆ d := subset_union_left.trans hd.1
  have hCA : C ⊆ d := subset_union_right.trans hd.1
  have himage {A : Set F} {T : Set X} (hAd : A ⊆ d)
      (hmem : ∀ z ∈ d ×ˢ I,k z ∈ T ↔ z.1 ∈ A) :
      k '' (d ×ˢ I) ∩ T = k '' (A ×ˢ I) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hx⟩
      exact ⟨z,⟨(hmem z hz).mp hx,hz.2⟩,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨⟨z,⟨hAd hz.1,hz.2⟩,rfl⟩,(hmem z ⟨hAd hz.1,hz.2⟩).mpr hz.1⟩
  refine ⟨k,hk,hki,?_,?_,fun z hz => ⟨P.inside (hGmap hz),hPO (hGmap hz)⟩,
    exists_chartwisePLBall_image (hd.prod (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)))
      (ContinuousLinearEquiv.ofFinrankEq (by simp)) hk Subset.rfl hki,
    hkU,hkC,himage hUA hkU,himage hCA hkC,?_,?_,?_⟩
  · intro z hz
    change P.map (r z.1,z.2) = _
    rw [←hrval ⟨z.1,hz.1⟩]
  · intro x hx
    change P.map (r x,0) = f x
    rw [P.central (r x) (hrmap hx),hj ⟨r x,hrmap hx⟩,hHr x hx]
  · apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hx⟩
      exact ⟨z,⟨⟨hz.1,(hkC z ⟨hUA hz.1,hz.2⟩).mp hx⟩,hz.2⟩,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨⟨z,⟨hz.1.1,hz.2⟩,rfl⟩,(hkC z ⟨hUA hz.1.1,hz.2⟩).mpr hz.1.2⟩
  · apply Subset.antisymm
    · intro x hx
      apply (himage hUA hkU).subset
      refine ⟨?_,hx.2⟩
      obtain ⟨z,hz,rfl⟩ := hx.1
      refine ⟨z,?_,rfl⟩
      rcases hz with hz | hz
      · exact ⟨hd.1 hz.1,hz.2⟩
      · exact ⟨hz.1,by rcases hz.2 with ht | ht <;> rw [ht] <;> norm_num⟩
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨⟨z,Or.inl ⟨Or.inl hz.1,hz.2⟩,rfl⟩,(hkU z ⟨hUA hz.1,hz.2⟩).mpr hz.1⟩
  · obtain ⟨x,hxd,hxq⟩ := hd.sdiff_nonempty
    refine ⟨k (x,1),⟨(x,1),Or.inr ⟨hxd,Or.inr rfl⟩,rfl⟩,?_⟩
    rintro ⟨z,hz,hzx⟩
    have heq := hki ⟨hUA hz.1,hz.2⟩ ⟨hxd,by norm_num⟩ hzx
    have hxU : x ∈ U := (show z.1 = x from congrArg Prod.fst heq) ▸ hz.1
    exact hxq (Or.inl hxU)

theorem exists_original_inside_block_base_rectangle
    {X α F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : α → OpenPartialHomeomorph X V3}
    {d U : Set F} {a b : F} (hU : IsFinitePLBallPair ℝ U {a,b}) (hab : a ≠ b)
    (hUd : U ⊆ d) {k : F × ℝ → X}
    (hk : PolyhedralPLInCharts e k (d ×ˢ I)) (hki : InjOn k (d ×ˢ I)) :
    ∃ r : P2 → X,
      PolyhedralPLInCharts e r (Icc (0 : ℝ) 1 ×ˢ I) ∧
      InjOn r (Icc (0 : ℝ) 1 ×ˢ I) ∧
      r '' (Icc (0 : ℝ) 1 ×ˢ I) = k '' (U ×ˢ I) ∧
      r '' (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ)) = k '' (U ×ˢ ({-1,1} : Set ℝ)) ∧
      (∀ t ∈ I,r (0,t) = k (a,t)) ∧ (∀ t ∈ I,r (1,t) = k (b,t)) ∧
      ∃ j : V2 → X, PolyhedralPLInCharts e j Disk ∧ InjOn j Disk ∧
        j '' Disk = k '' (U ×ˢ I) ∧
        j '' Rim = k '' (({a,b} ×ˢ I) ∪ (U ×ˢ ({-1,1} : Set ℝ))) := by
  obtain ⟨H,hH,hHa,hHb⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨u,hu,huval⟩ := hH
  have humap : MapsTo u (Icc (0 : ℝ) 1) U := by
    intro x hx
    rw [←huval ⟨x,hx⟩]
    exact (H ⟨x,hx⟩).property
  have hui : InjOn u (Icc (0 : ℝ) 1) := by
    intro x hx y hy heq
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((huval ⟨x,hx⟩).trans (heq.trans (huval ⟨y,hy⟩).symm))))
  have huimage : u '' Icc (0 : ℝ) 1 = U := by
    apply Subset.antisymm (image_subset_iff.mpr humap)
    intro x hx
    obtain ⟨z,hz⟩ := H.surjective ⟨x,hx⟩
    exact ⟨z,z.property,(huval z).symm.trans (congrArg Subtype.val hz)⟩
  have hua : u 0 = a := (huval ⟨0,by norm_num⟩).symm.trans hHa
  have hub : u 1 = b := (huval ⟨1,by norm_num⟩).symm.trans hHb
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJI,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    ⟨J,hJ,hJI,J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let G := Prod.map u (id : ℝ → ℝ)
  have hG : FinitePiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ I) := hu.prodMap hid
  have hGmap : MapsTo G (Icc (0 : ℝ) 1 ×ˢ I) (d ×ˢ I) :=
    fun z hz => ⟨hUd (humap hz.1),hz.2⟩
  let r := k ∘ G
  have hr : PolyhedralPLInCharts e r (Icc (0 : ℝ) 1 ×ˢ I) := by
    obtain ⟨K,hK,hKs,hKf⟩ := hG
    rw [←hKs]
    exact hk.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hKf⟩
      (fun z hz => hGmap (hKs.subset hz))
  have hri : InjOn r (Icc (0 : ℝ) 1 ×ˢ I) := by
    intro z hz w hw heq
    have hh := hki (hGmap hz) (hGmap hw) heq
    exact Prod.ext (hui hz.1 hw.1 (congrArg Prod.fst hh))
      (show z.2 = w.2 from congrArg (fun z : F × ℝ => z.2) hh)
  have hrimage : r '' (Icc (0 : ℝ) 1 ×ˢ I) = k '' (U ×ˢ I) := by
    apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨G z,⟨humap hz.1,hz.2⟩,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      obtain ⟨s,hs,huz⟩ := huimage.symm.subset hz.1
      exact ⟨(s,z.2),⟨hs,hz.2⟩,by change k (u s,z.2) = k z; rw [huz]⟩
  have hrSides : r '' (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ)) =
      k '' (U ×ˢ ({-1,1} : Set ℝ)) := by
    apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨G z,⟨humap hz.1,hz.2⟩,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      obtain ⟨s,hs,huz⟩ := huimage.symm.subset hz.1
      exact ⟨(s,z.2),⟨hs,hz.2⟩,by change k (u s,z.2) = k z; rw [huz]⟩
  have hDisk : IsFinitePLBallPair P2 Disk Rim :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨B,hB,hBboundary⟩ := hDisk.exists_homeomorph
    (hU.prod (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)))
  obtain ⟨v,hv,hvval⟩ := hB
  have hvmap : MapsTo v Disk (U ×ˢ I) := by
    intro x hx
    rw [←hvval ⟨x,hx⟩]
    exact (B ⟨x,hx⟩).property
  have hvi : InjOn v Disk := by
    intro x hx y hy heq
    exact congrArg Subtype.val (B.injective (Subtype.ext
      ((hvval ⟨x,hx⟩).trans (heq.trans (hvval ⟨y,hy⟩).symm))))
  have hvmap' : MapsTo v Disk (d ×ˢ I) := fun x hx => ⟨hUd (hvmap hx).1,(hvmap hx).2⟩
  have hj : PolyhedralPLInCharts e (k ∘ v) Disk := by
    obtain ⟨K,hK,hKs,hKf⟩ := hv
    rw [←hKs]
    exact hk.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hKf⟩
      (fun z hz => hvmap' (hKs.subset hz))
  refine ⟨r,hr,hri,hrimage,hrSides,?_,?_,k ∘ v,hj,hki.comp hvi hvmap',?_,?_⟩
  · intro t ht
    change k (u 0,t) = k (a,t)
    rw [hua]
  · intro t ht
    change k (u 1,t) = k (b,t)
    rw [hub]
  · apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨v z,hvmap hz,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      obtain ⟨y,hy⟩ := B.surjective ⟨z,hz⟩
      exact ⟨y,y.property,congrArg k ((hvval y).symm.trans (congrArg Subtype.val hy))⟩
  · apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      refine ⟨v z,?_,rfl⟩
      rw [←hvval ⟨z,sphere_subset_closedBall hz⟩]
      exact (hBboundary ⟨z,sphere_subset_closedBall hz⟩).mp hz
    · rintro x ⟨z,hz,rfl⟩
      have hzU : z ∈ U ×ˢ I :=
        (hU.prod (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))).1 hz
      obtain ⟨y,hy⟩ := B.surjective ⟨z,hzU⟩
      refine ⟨y,(hBboundary y).mpr ?_,congrArg k ((hvval y).symm.trans (congrArg Subtype.val hy))⟩
      exact (congrArg Subtype.val hy).symm ▸ hz

end PoincareConjecture.M76
