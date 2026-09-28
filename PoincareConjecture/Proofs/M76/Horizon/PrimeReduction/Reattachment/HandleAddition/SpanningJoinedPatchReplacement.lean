import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningEnlargedPatch
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalBallDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ClosedBallConfinement










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "Rect" => J ×ˢ I
local notation "Ends" => Set.prod ({0,1} : Set ℝ) (Icc (-1 : ℝ) 1)
local notation "Sides" => Set.prod (Icc (0 : ℝ) 1) ({-1,1} : Set ℝ)
local notation "Corners" => Set.prod ({0,1} : Set ℝ) ({-1,1} : Set ℝ)
local notation "RectRim" => Ends ∪ Sides
local notation "Wide" => Set.prod (Icc (-1 : ℝ) 2) (Icc (-1 : ℝ) 1)
local notation "WideRim" => Set.union (Set.prod ({-1,2} : Set ℝ) (Icc (-1 : ℝ) 1))
  (Set.prod (Icc (-1 : ℝ) 2) ({-1,1} : Set ℝ))



theorem exists_original_marked_joined_patch
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R E F S B T : Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (u : ChartwisePLBall e B T) (hBE : B ⊆ E) (hBR : B ⊆ interior R)
    (hFE : F ⊆ E)
    {a r : P2 → X} {k : P2 × ℝ → X}
    (ha : PolyhedralPLInCharts e a Rect) (hai : InjOn a Rect)
    (hr : PolyhedralPLInCharts e r Rect) (hri : InjOn r Rect)
    (hk : PolyhedralPLInCharts e k (Rect ×ˢ J)) (hki : InjOn k (Rect ×ˢ J))
    (hk0 : ∀ z ∈ Rect,k (z,0) = r z)
    (har : EqOn a r Ends)
    (hkE : ∀ z ∈ Rect ×ˢ J,k z ∈ E ↔ z.2 = 0)
    (hkS : ∀ z ∈ Rect ×ˢ J,k z ∈ S ↔ z.1.1 = 0 ∨ z.1.1 = 1)
    (hkR : k '' (Rect ×ˢ J) ⊆ interior R)
    (hBS : B ∩ S = a '' Rect) (haT : a '' Rect ⊆ T)
    (haF : ∀ z ∈ Rect,a z ∈ F ↔ z.1 = 0 ∨ z.1 = 1)
    (hrT : r '' Rect ⊆ T) (hTF : T ∩ F = r '' Rect)
    (hTout : (T \ r '' Rect).Nonempty)
    (v : ChartwisePLBall e (k '' (Rect ×ˢ J))
      (k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ))))) :
    IsFinitePLBallPair P2 Wide WideRim ∧
    ∃ (Q T' : Set X) (f : P2 → X),
      Nonempty (ChartwisePLBall e Q T') ∧ Q = B ∪ k '' (Rect ×ˢ J) ∧ Q ⊆ interior R ∧
      PolyhedralPLInCharts e f Wide ∧ InjOn f Wide ∧
      Q ∩ S = f '' Wide ∧ f '' Wide ⊆ T' ∧
      f '' Wide ∩ F = r '' Ends ∧ f '' WideRim ∩ F = r '' Corners ∧
      T' ∩ F = r '' RectRim ∧ (T' \ f '' Wide).Nonempty ∧
      (T' \ (f '' Wide \ f '' WideRim)) ∩ F = r '' Sides := by
  have hrect : IsFinitePLBallPair P2 Rect RectRim :=
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
      (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  have hends : Ends ⊆ Rect := fun z hz => hrect.1 (Or.inl hz)
  have hcorners : Corners ⊆ Ends := by
    intro z hz
    refine ⟨hz.1,?_⟩
    rcases hz.2 with h | h
    · rw [h]; norm_num
    · rw [mem_singleton_iff.mp h]; norm_num
  have hrF : r '' Rect ⊆ F := hTF.symm.subset.trans inter_subset_right
  have hrB : r '' Rect ⊆ B := hrT.trans u.boundary_subset
  have haE : a '' Rect ⊆ E := haT.trans (u.boundary_subset.trans hBE)
  have hkF (z : P2 × ℝ) (hz : z ∈ Rect ×ˢ J) : k z ∈ F ↔ z.2 = 0 := by
    constructor
    · exact fun h => (hkE z hz).mp (hFE h)
    · intro ht
      rw [show z = (z.1,0) from Prod.ext rfl ht,hk0 z.1 hz.1]
      exact hrF ⟨z.1,hz.1,rfl⟩
  have hbaseS (z : P2) (hz : z ∈ Rect) : r z ∈ S ↔ z.1 = 0 ∨ z.1 = 1 := by
    rw [←hk0 z hz]
    exact hkS (z,0) ⟨hz,by norm_num⟩
  have hcapB : B ∩ k '' (Rect ×ˢ J) = r '' Rect := by
    apply Subset.antisymm
    · rintro x ⟨hxB,z,hz,rfl⟩
      have ht := (hkE z hz).mp (hBE hxB)
      exact ⟨z.1,hz.1,by rw [show z = (z.1,0) from Prod.ext rfl ht,hk0 z.1 hz.1]⟩
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨hrB ⟨z,hz,rfl⟩,(hk0 z hz) ▸ ⟨(z,0),⟨hz,by norm_num⟩,rfl⟩⟩
  have hrCap : r '' Rect ⊆ k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ))) := by
    rintro x ⟨z,hz,rfl⟩
    exact ⟨(z,0),Or.inr ⟨hz,Or.inl rfl⟩,hk0 z hz⟩
  have hcapOut : (k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ))) \ r '' Rect).Nonempty := by
    refine ⟨k ((0,0),1),⟨((0,0),1),Or.inr ⟨by norm_num,by simp⟩,rfl⟩,?_⟩
    intro h
    have ht := (hkE ((0,0),1) (by norm_num)).mp (hFE (hrF h))
    norm_num at ht
  obtain ⟨joined⟩ := u.union_of_original_disk_contact he hR v
    (hBR.trans interior_subset) (hkR.trans interior_subset) hrect r hr hri hrT hrCap hTout hcapOut hcapB
  let Q := B ∪ k '' (Rect ×ˢ J)
  let T' := (T \ (r '' Rect \ r '' RectRim)) ∪
    ((k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ)))) \ (r '' Rect \ r '' RectRim))
  have hcapS : (k '' (Rect ×ˢ J)) ∩ S = k '' (Ends ×ˢ J) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hx⟩
      have h := (hkS z hz).mp hx
      exact ⟨z,⟨⟨h.elim Or.inl (fun h => Or.inr (mem_singleton_iff.mpr h)),hz.1.2⟩,hz.2⟩,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨⟨z,⟨hends hz.1,hz.2⟩,rfl⟩,(hkS z ⟨hends hz.1,hz.2⟩).mpr
        (hz.1.1.elim Or.inl (fun h => Or.inr (mem_singleton_iff.mp h)))⟩
  obtain ⟨hd,f,hf,hfi,hfa,hfimage,hfpoint,hfF,hfrF⟩ := exists_original_enlarged_spanning_patch
    he.compatible ha hai hk hki (fun t ht => (hk0 (0,t) ⟨by norm_num,ht⟩).trans
      (har ⟨by simp,ht⟩).symm) (fun t ht => (hk0 (1,t) ⟨by norm_num,ht⟩).trans
      (har ⟨by simp,ht⟩).symm) haE (fun z hz h => (hkE z hz).mp h) haF hkF
  have hQS : Q ∩ S = f '' Wide := by
    rw [show Q = B ∪ k '' (Rect ×ˢ J) from rfl,union_inter_distrib_right,hBS,hcapS,hfimage]
    rfl
  have hSrim (x : X) (hx : x ∈ r '' Rect) (hxS : x ∈ S) : x ∈ r '' RectRim := by
    rcases hx with ⟨z,hz,rfl⟩
    have h := (hbaseS z hz).mp hxS
    exact ⟨z,Or.inl ⟨h.elim Or.inl (fun h => Or.inr (mem_singleton_iff.mpr h)),hz.2⟩,rfl⟩
  have hfT : f '' Wide ⊆ T' := by
    rw [hfimage]
    rintro x (hx | hx)
    · exact Or.inl ⟨haT hx,fun h => h.2 (hSrim x h.1 (hBS.symm.subset hx).2)⟩
    · rcases hx with ⟨z,hz,rfl⟩
      have hzS := (hcapS.symm.subset ⟨z,hz,rfl⟩).2
      exact Or.inr ⟨⟨z,Or.inl ⟨Or.inl hz.1,hz.2⟩,rfl⟩,
        fun h => h.2 (hSrim _ h.1 hzS)⟩
  have hcapF : (k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ)))) ∩ F = r '' Rect := by
    apply Subset.antisymm
    · rintro x ⟨hx,hxF⟩
      obtain ⟨z,hz,rfl⟩ := v.boundary_subset hx
      have ht := (hkF z hz).mp hxF
      exact ⟨z.1,hz.1,by rw [show z = (z.1,0) from Prod.ext rfl ht,hk0 z.1 hz.1]⟩
    · exact fun x hx => ⟨hrCap hx,hrF hx⟩
  have hT'F : T' ∩ F = r '' RectRim := by
    apply Subset.antisymm
    · rintro x ⟨hx,hxF⟩
      rcases hx with hx | hx
      · by_contra hn; exact hx.2 ⟨hTF.subset ⟨hx.1,hxF⟩,hn⟩
      · by_contra hn; exact hx.2 ⟨hcapF.subset ⟨hx.1,hxF⟩,hn⟩
    · intro x hx
      have hxd := (image_mono hrect.1) hx
      exact ⟨Or.inl ⟨hrT hxd,fun h => h.2 hx⟩,hrF hxd⟩
  have hfF' : f '' Wide ∩ F = r '' Ends := hfF.trans (har.image_eq)
  have hfrF' : f '' WideRim ∩ F = r '' Corners := hfrF.trans ((har.mono hcorners).image_eq)
  have hT'out : (T' \ f '' Wide).Nonempty := by
    have hz : ((1/2,1) : P2) ∈ RectRim := Or.inr ⟨by norm_num,by simp⟩
    have hx := hT'F.symm.subset ⟨(1/2,1),hz,rfl⟩
    refine ⟨r (1/2,1),hx.1,?_⟩
    intro h
    have hxS := (hQS.symm.subset h).2
    have hbad := (hbaseS (1/2,1) (hrect.1 hz)).mp hxS
    norm_num at hbad
  refine ⟨hd,Q,T',f,⟨joined⟩,rfl,union_subset hBR hkR,hf,hfi,hQS,hfT,hfF',hfrF',hT'F,hT'out,?_⟩
  have himg : r '' Sides = (r '' RectRim \ r '' Ends) ∪ r '' Corners := by
    have hs : Sides = (RectRim \ Ends) ∪ Corners := by
      ext z
      simp only [mem_union,mem_sdiff]
      constructor
      · intro h
        by_cases hz : z.1=0 ∨ z.1=1
        · exact Or.inr ⟨hz,h.2⟩
        · exact Or.inl ⟨Or.inr h,fun hh => hz hh.1⟩
      · rintro (⟨h,hn⟩ | h)
        · rcases h with h | h
          · exact False.elim (hn h)
          · exact h
        · exact ⟨by rcases h.1 with h' | h' <;> rw [h'] <;> norm_num,h.2⟩
    conv_lhs => rw [hs]
    rw [image_union,(hri.mono hrect.1).image_sdiff_subset (fun z hz => Or.inl hz)]
  rw [himg]
  ext x
  have h0 := Set.ext_iff.mp hT'F x
  have h1 := Set.ext_iff.mp hfF' x
  have h2 := Set.ext_iff.mp hfrF' x
  have hc : x ∈ r '' Corners → x ∈ r '' RectRim :=
    fun h => (image_mono (hcorners.trans (fun z hz => Or.inl hz))) h
  have hcf : x ∈ r '' Corners → x ∈ F :=
    fun h => hrF ((image_mono (hcorners.trans hends)) h)
  simp only [mem_inter_iff,mem_sdiff,mem_union] at *
  tauto



theorem ChartwisePLSphere.exists_nonbounding_spanning_patch_replacement
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R E F S B T : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (hR : IsCompact R)
    (u : ChartwisePLBall e B T) (hBE : B ⊆ E) (hBR : B ⊆ interior R)
    (hFE : F ⊆ E) (hSR : S ⊆ interior R)
    {a r : P2 → X} {k : P2 × ℝ → X}
    (ha : PolyhedralPLInCharts e a Rect) (hai : InjOn a Rect)
    (hr : PolyhedralPLInCharts e r Rect) (hri : InjOn r Rect)
    (hk : PolyhedralPLInCharts e k (Rect ×ˢ J)) (hki : InjOn k (Rect ×ˢ J))
    (hk0 : ∀ z ∈ Rect,k (z,0) = r z) (har : EqOn a r Ends)
    (hkE : ∀ z ∈ Rect ×ˢ J,k z ∈ E ↔ z.2 = 0)
    (hkS : ∀ z ∈ Rect ×ˢ J,k z ∈ S ↔ z.1.1 = 0 ∨ z.1.1 = 1)
    (hkR : k '' (Rect ×ˢ J) ⊆ interior R)
    (hBS : B ∩ S = a '' Rect) (haT : a '' Rect ⊆ T)
    (haF : ∀ z ∈ Rect,a z ∈ F ↔ z.1 = 0 ∨ z.1 = 1)
    (hrT : r '' Rect ⊆ T) (hTF : T ∩ F = r '' Rect)
    (hTout : (T \ r '' Rect).Nonempty)
    (v : ChartwisePLBall e (k '' (Rect ×ˢ J))
      (k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ)))))
    (hnonbounding : ¬∃ H, H ⊆ R ∧ Nonempty (ChartwisePLBall e H S)) :
    ∃ (Q T' S' : Set X) (f : P2 → X) (g : V3 → X) (d q : Set V3),
      Nonempty (ChartwisePLBall e Q T') ∧ Q = B ∪ k '' (Rect ×ˢ J) ∧ Q ⊆ interior R ∧
      IsFinitePLBallPair P2 Wide WideRim ∧ PolyhedralPLInCharts e f Wide ∧ InjOn f Wide ∧
      Q ∩ S = f '' Wide ∧ f '' Wide ⊆ T' ∧
      IsFinitePLBallPair P2 d q ∧ PolyhedralPLInCharts e g d ∧ InjOn g d ∧
      g '' d = T' \ (f '' Wide \ f '' WideRim) ∧ g '' q = f '' WideRim ∧
      S' = (S \ (f '' Wide \ f '' WideRim)) ∪ g '' d ∧
      Nonempty (ChartwisePLSphere e S') ∧ S' ⊆ interior R ∧
      (¬∃ H, H ⊆ R ∧ Nonempty (ChartwisePLBall e H S')) ∧
      Q ∩ S' = g '' d ∧ g '' d ∩ F = r '' Sides ∧
      S' ∩ F = ((S ∩ F) \ (r '' Ends \ r '' Corners)) ∪ r '' Sides := by
  obtain ⟨hd,Q,T',f,⟨joined⟩,hQ,hQR,hf,hfi,hQS,hfT,hfF,hfrF,hTF',hTout',hside⟩ :=
    exists_original_marked_joined_patch he hR u hBE hBR hFE ha hai hr hri hk hki hk0 har
      hkE hkS hkR hBS haT haF hrT hTF hTout v
  have hSout : (S \ f '' Wide).Nonempty := by
    by_contra hn
    have hSQ : S ⊆ Q := by
      intro x hx
      have hxA : x ∈ f '' Wide := by
        by_contra hxA
        exact hn ⟨x,hx,hxA⟩
      exact (hQS.symm.subset hxA).1
    obtain ⟨H,hHQ,hH⟩ := s.exists_original_closed_ball_filling he.compatible joined hSQ
    exact hnonbounding ⟨H,hHQ.trans (hQR.trans interior_subset),hH⟩
  obtain ⟨_,g,_,_,d,q,_,hgd,_,hg,_,hgi,_,hgimage,_,hgrim,hnew,hQnew⟩ :=
    s.exists_original_ball_patch_replacement joined he.compatible hd f hf hfi hQS hfT hSout hTout'
  obtain ⟨_,_,hnon⟩ := s.nonbounding_original_ball_patch_replacement he hR joined hQR hSR
    hd f hf hfi hQS hfT hSout hTout' hnonbounding
  let S' := (S \ (f '' Wide \ f '' WideRim)) ∪ (T' \ (f '' Wide \ f '' WideRim))
  refine ⟨Q,T',S',f,g,d,q,⟨joined⟩,hQ,hQR,hd,hf,hfi,hQS,hfT,hgd,hg,hgi,hgimage,hgrim,
    ?_,hnew,union_subset (sdiff_subset.trans hSR)
      (sdiff_subset.trans (joined.boundary_subset.trans hQR)),hnon,?_,?_,?_⟩
  · rw [hgimage]
  · rw [hgimage]; exact hQnew
  · rw [hgimage]; exact hside
  · have hret : (S \ (f '' Wide \ f '' WideRim)) ∩ F =
        (S ∩ F) \ (r '' Ends \ r '' Corners) := by
      ext x
      have h0 := Set.ext_iff.mp hfF x
      have h1 := Set.ext_iff.mp hfrF x
      simp only [mem_inter_iff,mem_sdiff] at *
      tauto
    exact (union_inter_distrib_right _ _ _).trans (congrArg₂ (· ∪ ·) hret hside)

end PoincareConjecture.M76
