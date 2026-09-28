import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalSpherePatchReplacement
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "Rect" => J ×ˢ I
local notation "Wide" => Set.prod (Icc (-1 : ℝ) 2) (Icc (-1 : ℝ) 1)
local notation "WideRim" => Set.union (Set.prod ({-1,2} : Set ℝ) (Icc (-1 : ℝ) 1))
  (Set.prod (Icc (-1 : ℝ) 2) ({-1,1} : Set ℝ))

theorem exists_original_PL_map_union_of_disk_carriers
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {A B a b : Set E} (hA : IsFinitePLBallPair P2 A a) (hB : IsFinitePLBallPair P2 B b)
    {f g : E → X} (hf : PolyhedralPLInCharts e f A) (hg : PolyhedralPLInCharts e g B)
    (hag : ∀ x ∈ A ∩ B,f x = g x) :
    ∃ h : E → X,PolyhedralPLInCharts e h (A ∪ B) ∧ EqOn h f A ∧ EqOn h g B := by
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hA
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hB
  obtain ⟨h,hh,hf',hg'⟩ := _root_.Dehn.exists_circle_attachment_map_union he K L hK hL
    (hKs.symm ▸ hf) (hLs.symm ▸ hg)
    (fun x hx hy => hag x ⟨hKs.subset hx,hLs.subset hy⟩)
  exact ⟨h,by simpa only [hKs,hLs] using hh,hKs ▸ hf',hLs ▸ hg'⟩

theorem exists_original_three_panel_patch
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {a : P2 → X} {k : P2 × ℝ → X}
    (ha : PolyhedralPLInCharts e a Rect) (hai : InjOn a Rect)
    (hk : PolyhedralPLInCharts e k (Rect ×ˢ J)) (hki : InjOn k (Rect ×ˢ J))
    (hk0 : ∀ t ∈ I,k ((0,t),0) = a (0,t))
    (hk1 : ∀ t ∈ I,k ((1,t),0) = a (1,t))
    (htrace : ∀ z ∈ Rect ×ˢ J,k z ∈ a '' Rect → z.2 = 0) :
    ∃ f : P2 → X,PolyhedralPLInCharts e f Wide ∧ InjOn f Wide ∧
      (∀ z ∈ Icc (-1 : ℝ) 0 ×ˢ I,f z = k ((0,z.2),-z.1)) ∧
      (∀ z ∈ Rect,f z = a z) ∧
      ∀ z ∈ Icc (1 : ℝ) 2 ×ˢ I,f z = k ((1,z.2),z.1-1) := by
  let Left : Set P2 := Icc (-1 : ℝ) 0 ×ˢ I
  let Right : Set P2 := Icc (1 : ℝ) 2 ×ˢ I
  let MiddleLeft : Set P2 := Icc (-1 : ℝ) 1 ×ˢ I
  let AL : P2 →ᴬ[ℝ] (P2 × ℝ) :=
    ((ContinuousAffineMap.const ℝ P2 0).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).prod
      (-(ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)
  let AR : P2 →ᴬ[ℝ] (P2 × ℝ) :=
    ((ContinuousAffineMap.const ℝ P2 1).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap - ContinuousAffineMap.const ℝ P2 1)
  have hAL (z : P2) : AL z = ((0,z.2),-z.1) := rfl
  have hAR (z : P2) : AR z = ((1,z.2),z.1-1) := rfl
  have hALmap : MapsTo AL Left (Rect ×ˢ J) := by
    rintro z ⟨hz,ht⟩
    exact ⟨⟨by norm_num [hAL],ht⟩,⟨by change 0 ≤ -z.1; linarith [hz.2],
      by change -z.1 ≤ 1; linarith [hz.1]⟩⟩
  have hARmap : MapsTo AR Right (Rect ×ˢ J) := by
    rintro z ⟨hz,ht⟩
    exact ⟨⟨by norm_num [hAR],ht⟩,⟨by change 0 ≤ z.1-1; linarith [hz.1],
      by change z.1-1 ≤ 1; linarith [hz.2]⟩⟩
  have hrect (l u : ℝ) (hlu : l < u) :=
    (isFinitePLBallPair_Icc hlu).prod (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  have hcomp (B b : Set P2) (hB : IsFinitePLBallPair P2 B b)
      (A : P2 →ᴬ[ℝ] (P2 × ℝ)) (hmap : MapsTo A B (Rect ×ˢ J)) :
      PolyhedralPLInCharts e (k ∘ A) B := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hB
    rw [←hKs]
    exact hk.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine A).finitePiecewiseAffineOn hK)
      (fun z hz => hmap (hKs.subset hz))
  have hleft := hcomp _ _ (hrect (-1) 0 (by norm_num)) AL hALmap
  have hright := hcomp _ _ (hrect 1 2 (by norm_num)) AR hARmap
  have hLM : Left ∪ Rect = MiddleLeft := by
    ext z
    simp only [Left,MiddleLeft,mem_union,mem_prod,mem_Icc]
    constructor
    · rintro (⟨hz,ht⟩ | ⟨hz,ht⟩) <;> exact ⟨⟨by linarith [hz.1],by linarith [hz.2]⟩,ht⟩
    · rintro ⟨hz,ht⟩
      by_cases h : z.1 ≤ 0
      · exact Or.inl ⟨⟨hz.1,h⟩,ht⟩
      · exact Or.inr ⟨⟨by linarith,hz.2⟩,ht⟩
  obtain ⟨g,hg,hgL,hgM⟩ := exists_original_PL_map_union_of_disk_carriers he
    (hrect (-1) 0 (by norm_num)) (hrect 0 1 (by norm_num)) hleft ha (by
      intro z hz
      have hz0 : z.1 = 0 := by linarith [hz.1.1.2,hz.2.1.1]
      change k (AL z) = a z
      rw [hAL,hz0,neg_zero]
      exact (hk0 z.2 hz.1.2).trans (congrArg a (Prod.ext hz0.symm rfl)))
  have hgML : PolyhedralPLInCharts e g MiddleLeft := hLM ▸ hg
  have hwhole : MiddleLeft ∪ Right = Wide := by
    ext z
    simp only [MiddleLeft,Right,mem_union,mem_prod,mem_Icc]
    constructor
    · rintro (⟨hz,ht⟩ | ⟨hz,ht⟩) <;> exact ⟨⟨by linarith [hz.1],by linarith [hz.2]⟩,ht⟩
    · rintro ⟨hz,ht⟩
      by_cases h : z.1 ≤ 1
      · exact Or.inl ⟨⟨hz.1,h⟩,ht⟩
      · exact Or.inr ⟨⟨by linarith,hz.2⟩,ht⟩
  obtain ⟨f,hf,hfML,hfR⟩ := exists_original_PL_map_union_of_disk_carriers he
    (hrect (-1) 1 (by norm_num)) (hrect 1 2 (by norm_num)) hgML hright (by
      intro z hz
      have hz1 : z.1 = 1 := by linarith [hz.1.1.2,hz.2.1.1]
      rw [hgM ⟨by rw [hz1]; norm_num,hz.1.2⟩]
      change a z = k (AR z)
      rw [hAR,hz1,sub_self]
      exact (congrArg a (show z = (1,z.2) from Prod.ext hz1 rfl)).trans (hk1 z.2 hz.1.2).symm)
  have hfL (z : P2) (hz : z ∈ Left) : f z = k (AL z) :=
    (hfML (hLM.subset (Or.inl hz))).trans (hgL hz)
  have hfM (z : P2) (hz : z ∈ Rect) : f z = a z :=
    (hfML (hLM.subset (Or.inr hz))).trans (hgM hz)
  have hfR' (z : P2) (hz : z ∈ Right) : f z = k (AR z) := hfR hz
  have hALi : Function.Injective AL := by
    intro z w h
    have h1 := congrArg Prod.snd h
    have h2 := congrArg (fun p : P2 × ℝ => p.1.2) h
    exact Prod.ext (neg_injective h1) h2
  have hARi : Function.Injective AR := by
    intro z w h
    have h1 := congrArg Prod.snd h
    have h2 := congrArg (fun p : P2 × ℝ => p.1.2) h
    change z.1-1 = w.1-1 at h1
    exact Prod.ext (by linarith) h2
  have hcrossL (z w : P2) (hz : z ∈ Left) (hw : w ∈ Rect) (h : f z = f w) : z = w := by
    have hkw : k (AL z) = a w := (hfL z hz).symm.trans (h.trans (hfM w hw))
    have hz0 : z.1 = 0 := neg_eq_zero.mp (htrace _ (hALmap hz) ⟨w,hw,hkw.symm⟩)
    have hzw : a (0,z.2) = a w := by simpa only [hAL,hz0,neg_zero,hk0 z.2 hz.2] using hkw
    have h : (0,z.2) = w := @hai (0,z.2) ⟨by norm_num,hz.2⟩ w hw hzw
    exact (show z = (0,z.2) from Prod.ext hz0 rfl).trans h
  have hcrossR (z w : P2) (hz : z ∈ Right) (hw : w ∈ Rect) (h : f z = f w) : z = w := by
    have hkw : k (AR z) = a w := (hfR' z hz).symm.trans (h.trans (hfM w hw))
    have hz1 : z.1 = 1 := sub_eq_zero.mp (htrace _ (hARmap hz) ⟨w,hw,hkw.symm⟩)
    have hzw : a (1,z.2) = a w := by simpa only [hAR,hz1,sub_self,hk1 z.2 hz.2] using hkw
    have h : (1,z.2) = w := @hai (1,z.2) ⟨by norm_num,hz.2⟩ w hw hzw
    exact (show z = (1,z.2) from Prod.ext hz1 rfl).trans h
  have hseparate (z w : P2) (hz : z ∈ Left) (hw : w ∈ Right) : f z ≠ f w := by
    intro h
    have hcoord := hki (hALmap hz) (hARmap hw) ((hfL z hz).symm.trans (h.trans (hfR' w hw)))
    have hbad := congrArg (fun p : P2 × ℝ => p.1.1) hcoord
    norm_num [hAL,hAR] at hbad
  refine ⟨f,hwhole ▸ hf,?_,hfL,hfM,hfR'⟩
  intro z hz w hw h
  have hparts (y : P2) (hy : y ∈ Wide) : y ∈ Left ∨ y ∈ Rect ∨ y ∈ Right := by
    rcases hwhole.symm.subset hy with hm | hr
    · rcases hLM.symm.subset hm with hl | hm
      · exact Or.inl hl
      · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hr)
  rcases hparts z hz with hz | hz | hz <;> rcases hparts w hw with hw | hw | hw
  · exact hALi (hki (hALmap hz) (hALmap hw) ((hfL z hz).symm.trans (h.trans (hfL w hw))))
  · exact hcrossL z w hz hw h
  · exact False.elim (hseparate z w hz hw h)
  · exact (hcrossL w z hw hz h.symm).symm
  · exact hai hz hw ((hfM z hz).symm.trans (h.trans (hfM w hw)))
  · exact (hcrossR w z hw hz h.symm).symm
  · exact False.elim (hseparate w z hw hz h.symm)
  · exact hcrossR z w hz hw h
  · exact hARi (hki (hARmap hz) (hARmap hw) ((hfR' z hz).symm.trans (h.trans (hfR' w hw))))

theorem exists_original_enlarged_spanning_patch
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {a : P2 → X} {k : P2 × ℝ → X} {E F : Set X}
    (ha : PolyhedralPLInCharts e a Rect) (hai : InjOn a Rect)
    (hk : PolyhedralPLInCharts e k (Rect ×ˢ J)) (hki : InjOn k (Rect ×ˢ J))
    (hk0 : ∀ t ∈ I,k ((0,t),0) = a (0,t))
    (hk1 : ∀ t ∈ I,k ((1,t),0) = a (1,t))
    (haE : a '' Rect ⊆ E)
    (hkE : ∀ z ∈ Rect ×ˢ J,k z ∈ E → z.2 = 0)
    (haF : ∀ z ∈ Rect,a z ∈ F ↔ z.1 = 0 ∨ z.1 = 1)
    (hkF : ∀ z ∈ Rect ×ˢ J,k z ∈ F ↔ z.2 = 0) :
    IsFinitePLBallPair P2 Wide WideRim ∧
    ∃ f : P2 → X,PolyhedralPLInCharts e f Wide ∧ InjOn f Wide ∧
      EqOn f a Rect ∧
      f '' Wide = a '' Rect ∪ k '' ((({0,1} : Set ℝ) ×ˢ I) ×ˢ J) ∧
      (∀ z ∈ Wide,f z ∈ F ↔ z.1 = 0 ∨ z.1 = 1) ∧
      f '' Wide ∩ F = a '' (({0,1} : Set ℝ) ×ˢ I) ∧
      f '' WideRim ∩ F = a '' (({0,1} : Set ℝ) ×ˢ ({-1,1} : Set ℝ)) := by
  have hpair : IsFinitePLBallPair P2 Wide WideRim :=
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 2)).prod
      (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  obtain ⟨f,hf,hfi,hfL,hfM,hfR⟩ := exists_original_three_panel_patch he ha hai hk hki hk0 hk1
    (fun z hz hza => hkE z hz (haE hza))
  have hRW : Rect ⊆ Wide := fun z hz => ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩
  have hFpoint (z : P2) (hz : z ∈ Wide) : f z ∈ F ↔ z.1 = 0 ∨ z.1 = 1 := by
    by_cases h0 : z.1 ≤ 0
    · rw [hfL z ⟨⟨hz.1.1,h0⟩,hz.2⟩,hkF _ ⟨⟨by norm_num,hz.2⟩,
        ⟨by linarith,by linarith [hz.1.1]⟩⟩]
      change -z.1=0 ↔ z.1=0 ∨ z.1=1
      constructor
      · intro h; exact Or.inl (neg_eq_zero.mp h)
      · rintro (h | h) <;> linarith
    by_cases h1 : z.1 ≤ 1
    · have hzR : z ∈ Rect := ⟨⟨by linarith,h1⟩,hz.2⟩
      rw [hfM z hzR,haF z hzR]
    · rw [hfR z ⟨⟨by linarith,hz.1.2⟩,hz.2⟩,hkF _ ⟨⟨by norm_num,hz.2⟩,
        ⟨by linarith,by linarith [hz.1.2]⟩⟩]
      change z.1-1=0 ↔ z.1=0 ∨ z.1=1
      constructor
      · intro h; exact Or.inr (sub_eq_zero.mp h)
      · rintro (h | h) <;> linarith
  have hendR {z : P2} (hz : z ∈ ({0,1} : Set ℝ) ×ˢ I) : z ∈ Rect := by
    refine ⟨?_,hz.2⟩
    rcases hz.1 with h | h
    · rw [h]; norm_num
    · rw [mem_singleton_iff.mp h]; norm_num
  have hpointR {z : P2} (hz : z ∈ Wide) (h : z.1=0 ∨ z.1=1) : z ∈ Rect := by
    rcases h with h | h <;> exact ⟨by rw [h]; norm_num,hz.2⟩
  refine ⟨hpair,f,hf,hfi,hfM,?_,hFpoint,?_,?_⟩
  · apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      by_cases h0 : z.1 ≤ 0
      · rw [hfL z ⟨⟨hz.1.1,h0⟩,hz.2⟩]
        exact Or.inr ⟨((0,z.2),-z.1),⟨⟨by simp,hz.2⟩,by constructor <;> linarith [hz.1.1]⟩,rfl⟩
      by_cases h1 : z.1 ≤ 1
      · have hzR : z ∈ Rect := ⟨⟨by linarith,h1⟩,hz.2⟩
        rw [hfM z hzR]
        exact Or.inl ⟨z,hzR,rfl⟩
      · rw [hfR z ⟨⟨by linarith,hz.1.2⟩,hz.2⟩]
        exact Or.inr ⟨((1,z.2),z.1-1),⟨⟨by simp,hz.2⟩,by constructor <;> linarith [hz.1.2]⟩,rfl⟩
    · rintro x (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩)
      · exact ⟨z,hRW hz,hfM z hz⟩
      · rcases hz.1.1 with h | h
        · refine ⟨(-z.2,z.1.2),⟨⟨by linarith [hz.2.2],by linarith [hz.2.1]⟩,hz.1.2⟩,?_⟩
          rw [hfL (-z.2,z.1.2) ⟨⟨by linarith [hz.2.2],by linarith [hz.2.1]⟩,hz.1.2⟩]
          simp only [neg_neg]
          exact congrArg k (Prod.ext (Prod.ext h.symm rfl) rfl)
        · have h1 := mem_singleton_iff.mp h
          refine ⟨(1+z.2,z.1.2),⟨⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩,hz.1.2⟩,?_⟩
          rw [hfR (1+z.2,z.1.2) ⟨⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩,hz.1.2⟩]
          exact congrArg k (Prod.ext (Prod.ext h1.symm rfl) (by ring))
  · apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hxF⟩
      have hz01 := (hFpoint z hz).mp hxF
      refine ⟨z,⟨?_,hz.2⟩,(hfM z (hpointR hz hz01)).symm⟩
      exact hz01.elim (fun h => Or.inl h) (fun h => Or.inr (mem_singleton_iff.mpr h))
    · rintro x ⟨z,hz,rfl⟩
      have hzR := hendR hz
      refine ⟨⟨z,hRW hzR,hfM z hzR⟩,(haF z hzR).mpr ?_⟩
      exact hz.1.elim Or.inl (fun h => Or.inr (mem_singleton_iff.mp h))
  · apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hxF⟩
      have hzW := hpair.1 hz
      have hz01 := (hFpoint z hzW).mp hxF
      have hzt : z.2 ∈ ({-1,1} : Set ℝ) := by
        rcases hz with hz | hz
        · rcases hz.1 with h | h
          · rcases hz01 with h' | h' <;> linarith
          · have h2 := mem_singleton_iff.mp h
            rcases hz01 with h' | h' <;> linarith
        · exact hz.2
      refine ⟨z,⟨?_,hzt⟩,(hfM z (hpointR hzW hz01)).symm⟩
      exact hz01.elim Or.inl (fun h => Or.inr (mem_singleton_iff.mpr h))
    · rintro x ⟨z,hz,rfl⟩
      have hzt : z.2 ∈ I := by
        rcases hz.2 with h | h
        · rw [h]; norm_num
        · rw [mem_singleton_iff.mp h]; norm_num
      have hzR := hendR ⟨hz.1,hzt⟩
      refine ⟨⟨z,Or.inr ⟨(hRW hzR).1,hz.2⟩,hfM z hzR⟩,(haF z hzR).mpr ?_⟩
      exact hz.1.elim Or.inl (fun h => Or.inr (mem_singleton_iff.mp h))

end PoincareConjecture.M76
