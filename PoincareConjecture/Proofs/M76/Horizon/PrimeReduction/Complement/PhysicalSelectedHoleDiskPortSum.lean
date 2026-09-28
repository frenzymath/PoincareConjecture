import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PhysicalSelectedHoleNormalization

set_option autoImplicit false

open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

open PoincareConjecture.M76.HamiltonIndexTwoStandard

theorem exists_physical_selected_hole_disk_port_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Bool → Type*} [∀ b, Finite (ι b)]
    (R : Bool → Set E) (a r : ∀ b, ι b → Set V4)
    (ha : ∀ b j, IsFinitePLBallPair V3 (a b j) (r b j))
    (haS : ∀ b j, a b j ⊆ sphere)
    (hopen : ∀ b j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a b j \ r b j)))
    (hdis : ∀ b, Pairwise fun j k => Disjoint (a b j) (a b k)) (i : ∀ b, ι b)
    (C : ∀ b, R b ≃ₜ (sphere \ ⋃ j, a b j \ r b j : Set V4))
    (hC : ∀ b, (C b).IsFinitePL)
    {d q : Set E} (hd : IsFinitePLBallPair P2 d q)
    (hcontact : R false ∩ R true = d)
    (hport : ∀ b (x : R b), (x : E) ∈ d → (C b x : V4) ∈ r b (i b))
    (hout : ∀ b, ∃ x : R b, (C b x : V4) ∈ r b (i b) ∧ (x : E) ∉ d) :
    let s : Bool → Set E := fun b => (Subtype.val : R b → E) ''
      ((fun x : R b => (C b x : V4)) ⁻¹' r b (i b))
    let outer := (s false \ (d \ q)) ∪ (s true \ (d \ q))
    let J := (b : Bool) × {j : ι b // j ≠ i b}
    let m : J → Set E := fun j => (Subtype.val : R j.1 → E) ''
      ((fun x : R j.1 => (C j.1 x : V4)) ⁻¹' r j.1 j.2)
    ∃ c t : J → Set V4,
      (∀ j, IsFinitePLBallPair V3 (c j) (t j)) ∧
      (∀ j, c j ⊆ lower \ seam) ∧ (∀ j, Disjoint upper (c j)) ∧
      Pairwise (fun j k => Disjoint (c j) (c k)) ∧
      ∃ (L : SimplicialComplex ℝ E)
        (F : (R false ∪ R true : Set E) ≃ₜ
          (sphere \ ((upper \ seam) ∪ ⋃ j, c j \ t j) : Set V4)),
        L.faces.Finite ∧ L.space = R false ∪ R true ∧ F.IsFinitePL ∧
        (∀ j (x : (R false ∪ R true : Set E)), (x : E) ∈ m j ↔ (F x : V4) ∈ t j) ∧
        (∀ j, (fun x : (R false ∪ R true : Set E) => (F x : V4)) ''
          ((Subtype.val : (R false ∪ R true : Set E) → E) ⁻¹' m j) = t j) ∧
        (∀ x : (R false ∪ R true : Set E), (x : E) ∈ outer ↔ (F x : V4) ∈ seam) ∧
        (fun x : (R false ∪ R true : Set E) => (F x : V4)) ''
          ((Subtype.val : (R false ∪ R true : Set E) → E) ⁻¹' outer) = seam := by
  dsimp only
  let B := fun b => sphere \ (a b (i b) \ r b (i b))
  let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
  let S := fun b : Bool => if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
    else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
  let J := (b : Bool) × {j : ι b // j ≠ i b}
  let p := fun b => sphere \ ⋃ j, a b j \ r b j
  let m : J → Set E := fun j => (Subtype.val : R j.1 → E) ''
    ((fun x : R j.1 => (C j.1 x : V4)) ⁻¹' r j.1 j.2)
  let s : Bool → Set E := fun b => (Subtype.val : R b → E) ''
    ((fun x : R b => (C b x : V4)) ⁻¹' r b (i b))
  let outer := (s false \ (d \ q)) ∪ (s true \ (d \ q))
  obtain ⟨f,n,N,hcharts,hnorm,hagree,hnport,hnrim⟩ :=
    exists_physical_selected_hole_normalization R a r ha haS hopen hdis i C hC hd hcontact hport hout
  let c : J → Set P3 := fun j => n j.1 '' a j.1 j.2
  let t : J → Set P3 := fun j => n j.1 '' r j.1 j.2
  let Q := fun b => P b \ ⋃ j : {j : ι b // j ≠ i b}, (n b '' a b j) \ (n b '' r b j)
  have hB (b : Bool) := selected_hole_punctured_ball
    (a b) (r b) (ha b) (haS b) (hopen b) (hdis b) (i b)
  have hholes (b : Bool) (j : {j : ι b // j ≠ i b}) :
      IsFinitePLBallPair V3 (n b '' a b j) (n b '' r b j) ∧
        n b '' a b j ⊆ P b \ S b := by
    have hj := (hB b).2.1 j
    refine ⟨(ha b j).image_of_subset (hnorm b).2.1 (hj.trans sdiff_subset)
      (hnorm b).2.2.1, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    have hv := (hnorm b).2.2.2.1 ⟨x,(hj hx).1⟩
    refine ⟨hv ▸ (N b ⟨x,(hj hx).1⟩).property,?_⟩
    intro hs
    exact (hj hx).2 (((hnorm b).2.2.2.2 _).mpr (hv.symm ▸ hs))
  have hPinter : P false ∩ P true = endDisk 0 := by
    ext x
    change ((x.1 ∈ CoordinateHalfBoxes.base 1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∧
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1)) ↔
      x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = 0
    constructor
    · intro hx
      exact ⟨hx.1.1,le_antisymm hx.1.2.2 hx.2.2.1⟩
    · rintro ⟨hx,heq⟩
      rw [heq]
      exact ⟨⟨hx,by norm_num⟩,hx,by norm_num⟩
  have hdP (b : Bool) : endDisk 0 ⊆ P b := by
    cases b
    · exact fun _ hx => (hPinter.symm.subset hx).1
    · exact fun _ hx => (hPinter.symm.subset hx).2
  have hdS (b : Bool) : endDisk 0 ⊆ S b := by
    cases b
    · exact subset_union_right
    · exact subset_union_right.trans subset_union_left
  have hcross (b : Bool) (j : {j : ι b // j ≠ i b}) :
      Disjoint (n b '' a b j) (P (!b)) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hi : x ∈ endDisk 0 := by
      cases b
      · exact hPinter.subset ⟨((hholes false j).2 hx).1,hy⟩
      · exact hPinter.subset ⟨hy,((hholes true j).2 hx).1⟩
    exact ((hholes b j).2 hx).2 (hdS b hi)
  have hcdis : Pairwise fun j k : J => Disjoint (c j) (c k) := by
    have hsame (b : Bool) : Pairwise fun j k : {j : ι b // j ≠ i b} =>
        Disjoint (n b '' a b j) (n b '' a b k) := by
      intro j k hjk
      apply disjoint_left.mpr
      rintro _ ⟨x,hx,hxy⟩ ⟨z,hz,hzy⟩
      have hxz := (hnorm b).2.2.1 ((hB b).2.1 j hx).1 ((hB b).2.1 k hz).1
        (hxy.trans hzy.symm)
      exact disjoint_left.mp (hdis b (Subtype.val_injective.ne hjk)) hx (hxz.symm ▸ hz)
    rintro ⟨b,j⟩ ⟨b',k⟩ hne
    cases b <;> cases b'
    · exact hsame false (fun hjk => hne (by cases hjk; rfl))
    · exact (hcross false j).mono_right ((hholes true k).2.trans sdiff_subset)
    · exact (hcross true j).mono_right ((hholes false k).2.trans sdiff_subset)
    · exact hsame true (fun hjk => hne (by cases hjk; rfl))
  have hside (j : J) : c j ⊆ prism (-1) 0 \ S false ∨
      c j ⊆ prism 0 1 \ S true := by
    rcases j with ⟨b,j⟩
    cases b
    · exact Or.inl (hholes false j).2
    · exact Or.inr (hholes true j).2
  have hout₀ : (S false \ endDisk 0).Nonempty := by
    refine ⟨((0,0),-1),Or.inl (Or.inr ?_),?_⟩
    · norm_num [endDisk,CoordinateHalfBoxes.base]
    · intro hx
      have hh : (-1 : ℝ) = 0 := hx.2
      norm_num at hh
  have hout₁ : (S true \ endDisk 0).Nonempty := by
    refine ⟨((0,0),1),Or.inr ?_,?_⟩
    · norm_num [endDisk,CoordinateHalfBoxes.base]
    · intro hx
      have hh : (1 : ℝ) = 0 := hx.2
      norm_num at hh
  obtain ⟨_,g,_,_,_,_,hgball,hgin,hgout,hgdis,
      _,G,_,_,hG,_,hGmem,hGimage,hGouter⟩ :=
    (prism_ballPair (by norm_num : (-1 : ℝ) < 0)).exists_punctured_sphere_of_disk_port_sum
      (prism_ballPair (by norm_num : (0 : ℝ) < 1)) (endDisk_ballPair 0)
      (hdS false) (hdS true) hout₀ hout₁ hPinter c t (fun j => (hholes j.1 j.2).1) hside hcdis
  have hrestricted (b : Bool) : ∃ e : p b ≃ₜ Q b, e.IsFinitePL ∧
      (∀ x : p b, (e x : P3) = n b x) ∧
      ∀ j : {j : ι b // j ≠ i b}, ∀ x : p b,
        (x : V4) ∈ r b j ↔ (e x : P3) ∈ n b '' r b j := by
    have hp := (hB b).2.2.1
    obtain ⟨e,he,hval,hmark⟩ := restrict_punctured_ball (hB b).1
      (fun j : {j : ι b // j ≠ i b} => a b j) (fun j => r b j)
      (fun j => ha b j) (hB b).2.1
      (fun j k hjk => hdis b (Subtype.val_injective.ne hjk))
      (N b) (hnorm b).1 (n b) (hnorm b).2.1 (hnorm b).2.2.1 (hnorm b).2.2.2.1
    exact ⟨(Homeomorph.setCongr hp.symm).trans e,he.setCongr hp rfl,
      (fun x => hval ⟨x,hp.symm.subset x.property⟩),
      fun j x => hmark j ⟨x,hp.symm.subset x.property⟩⟩
  choose u hu huval humark using hrestricted
  let e (b : Bool) : R b ≃ₜ Q b := (C b).trans (u b)
  have he (b : Bool) : (e b).IsFinitePL := (hC b).trans (hu b)
  have heval (b : Bool) (x : R b) : (e b x : P3) = n b (f b x) :=
    (huval b (C b x)).trans (congrArg (n b) ((hcharts b).2.2 x))
  have heport (b : Bool) (x : R b) : (x : E) ∈ d ↔ (e b x : P3) ∈ endDisk 0 := by
    rw [heval]
    exact hnport b x
  have hdQ (b : Bool) : endDisk 0 ⊆ Q b := by
    intro x hx
    refine ⟨hdP b hx,?_⟩
    intro hh
    obtain ⟨j,hj,_⟩ := mem_iUnion.mp hh
    exact ((hholes b j).2 hj).2 (hdS b hx)
  have hQinter : Q false ∩ Q true = endDisk 0 := by
    apply Subset.antisymm
    · exact fun _ hx => hPinter.subset ⟨hx.1.1,hx.2.1⟩
    · exact fun _ hx => ⟨hdQ false hx,hdQ true hx⟩
  have hoverlap (x : R false) : (x : E) ∈ R true ↔ (e false x : P3) ∈ Q true := by
    constructor
    · intro hx
      exact hdQ true ((heport false x).mp (hcontact.subset ⟨x.property,hx⟩))
    · intro hx
      exact (hcontact.symm.subset ((heport false x).mpr
        (hQinter.subset ⟨(e false x).property,hx⟩))).2
  obtain ⟨U,hU,hUfalse,hUtrue⟩ := Homeomorph.exists_union_finitePL
    (e false) (e true) (he false) (he true) hoverlap
    (fun x hx hy => (heval false ⟨x,hx⟩).trans
      ((hagree (hcontact.subset ⟨hx,hy⟩)).trans (heval true ⟨x,hy⟩).symm))
  have hkeep (b : Bool) (x : R b) :
      (U ⟨x,by cases b; exact Or.inl x.property; exact Or.inr x.property⟩ : P3) = e b x := by
    cases b
    · exact hUfalse x
    · exact hUtrue x
  have hQunion : Q false ∪ Q true =
      (prism (-1) 0 ∪ prism 0 1) \ ⋃ j : J, c j \ t j := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · refine ⟨Or.inl hx.1,?_⟩
        intro hh
        obtain ⟨⟨b,j⟩,hj,hnr⟩ := mem_iUnion.mp hh
        cases b
        · exact hx.2 (mem_iUnion.mpr ⟨j,hj,hnr⟩)
        · exact disjoint_left.mp (hcross true j) hj hx.1
      · refine ⟨Or.inr hx.1,?_⟩
        intro hh
        obtain ⟨⟨b,j⟩,hj,hnr⟩ := mem_iUnion.mp hh
        cases b
        · exact disjoint_left.mp (hcross false j) hj hx.1
        · exact hx.2 (mem_iUnion.mpr ⟨j,hj,hnr⟩)
    · intro x hx
      rcases hx.1 with hxf | hxt
      · refine Or.inl ⟨hxf,?_⟩
        intro hh
        obtain ⟨j,hj⟩ := mem_iUnion.mp hh
        exact hx.2 (mem_iUnion.mpr ⟨⟨false,j⟩,hj⟩)
      · refine Or.inr ⟨hxt,?_⟩
        intro hh
        obtain ⟨j,hj⟩ := mem_iUnion.mp hh
        exact hx.2 (mem_iUnion.mpr ⟨⟨true,j⟩,hj⟩)
  let U' := U.trans (Homeomorph.setCongr hQunion)
  have hU' : U'.IsFinitePL := hU.setCongr rfl hQunion
  let F := U'.trans G
  have hF : F.IsFinitePL := hU'.trans hG
  have hmR (j : J) : m j ⊆ R j.1 := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hmrim (j : J) (x : R j.1) : (x : E) ∈ m j ↔ (C j.1 x : V4) ∈ r j.1 j.2 := by
    constructor
    · rintro ⟨y,hy,hyx⟩
      exact (congrArg (fun z : R j.1 => (C j.1 z : V4)) (Subtype.ext hyx)) ▸ hy
    · exact fun hx => ⟨x,hx,rfl⟩
  have hmark (j : J) (x : R j.1) : (x : E) ∈ m j ↔ (e j.1 x : P3) ∈ t j :=
    (hmrim j x).trans (humark j.1 j.2 (C j.1 x))
  have htQ (j : J) : t j ⊆ Q j.1 := by
    rintro _ ⟨x,hx,rfl⟩
    have hxp := (hB j.1).2.2.2 j.2 hx
    rw [← huval j.1 ⟨x,hxp⟩]
    exact (u j.1 ⟨x,hxp⟩).property
  have hUm (j : J) (x : (R false ∪ R true : Set E)) :
      (x : E) ∈ m j ↔ (U x : P3) ∈ t j := by
    let er := (e j.1).restrictSubsets (hmR j) (htQ j) (hmark j)
    have hRU (b : Bool) : R b ⊆ R false ∪ R true := by
      cases b
      · exact subset_union_left
      · exact subset_union_right
    have hQU (b : Bool) : Q b ⊆ Q false ∪ Q true := by
      cases b
      · exact subset_union_left
      · exact subset_union_right
    exact U.mem_subset_iff_of_extension er ((hmR j).trans (hRU j.1))
      ((htQ j).trans (hQU j.1))
      (fun y => Subtype.ext (hkeep j.1 ⟨y,hmR j y.property⟩)) x
  have hFmem (j : J) (x : (R false ∪ R true : Set E)) :
      (x : E) ∈ m j ↔ (F x : V4) ∈ g '' t j :=
    (hUm j x).trans (hGmem j (U' x))
  have hsR (b : Bool) : s b ⊆ R b := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have hSQ (b : Bool) : S b ⊆ Q b := by
    intro x hx
    have hSP : S b ⊆ P b := by
      cases b
      · exact (prism_ballPair (by norm_num : (-1 : ℝ) < 0)).1
      · exact (prism_ballPair (by norm_num : (0 : ℝ) < 1)).1
    refine ⟨hSP hx,?_⟩
    rintro hh
    obtain ⟨j,hj,_⟩ := mem_iUnion.mp hh
    exact ((hholes b j).2 hj).2 hx
  have hes (b : Bool) (x : R b) : (x : E) ∈ s b ↔ (e b x : P3) ∈ S b := by
    have hsrim : (x : E) ∈ s b ↔ (C b x : V4) ∈ r b (i b) := by
      constructor
      · rintro ⟨y,hy,hyx⟩
        exact (congrArg (fun z : R b => (C b z : V4)) (Subtype.ext hyx)) ▸ hy
      · exact fun hx => ⟨x,hx,rfl⟩
    have hCxB : (C b x : V4) ∈ B b :=
      ⟨(C b x).property.1,fun hh => (C b x).property.2 (mem_iUnion.mpr ⟨i b,hh⟩)⟩
    have hselected := (hnorm b).2.2.2.2 ⟨C b x,hCxB⟩
    rw [(hnorm b).2.2.2.1] at hselected
    exact hsrim.trans (hselected.trans (by rw [show (e b x : P3) = n b (C b x) from huval b (C b x)]))
  have hUs (b : Bool) (x : (R false ∪ R true : Set E)) :
      (x : E) ∈ s b ↔ (U x : P3) ∈ S b := by
    let er := (e b).restrictSubsets (hsR b) (hSQ b) (hes b)
    have hRU : R b ⊆ R false ∪ R true := by
      cases b
      · exact subset_union_left
      · exact subset_union_right
    have hQU : Q b ⊆ Q false ∪ Q true := by
      cases b
      · exact subset_union_left
      · exact subset_union_right
    exact U.mem_subset_iff_of_extension er ((hsR b).trans hRU) ((hSQ b).trans hQU)
      (fun y => Subtype.ext (hkeep b ⟨y,hsR b y.property⟩)) x
  have hUport (x : (R false ∪ R true : Set E)) :
      ((x : E) ∈ d ↔ (U x : P3) ∈ endDisk 0) ∧
      ((x : E) ∈ q ↔ (U x : P3) ∈ endRim 0) := by
    have hside (b : Bool) (hx : (x : E) ∈ R b) :
        ((x : E) ∈ d ↔ (U x : P3) ∈ endDisk 0) ∧
        ((x : E) ∈ q ↔ (U x : P3) ∈ endRim 0) := by
      have hv : (U x : P3) = n b (f b x) :=
        (hkeep b ⟨x,hx⟩).trans (heval b ⟨x,hx⟩)
      rw [hv]
      exact ⟨hnport b ⟨x,hx⟩,hnrim b ⟨x,hx⟩⟩
    rcases x.property with hx | hx
    · exact hside false hx
    · exact hside true hx
  have hUouter (x : (R false ∪ R true : Set E)) :
      (x : E) ∈ outer ↔ (U' x : P3) ∈
        (S false \ (endDisk 0 \ endRim 0)) ∪ (S true \ (endDisk 0 \ endRim 0)) := by
    change ((x : E) ∈ s false ∧ ¬ ((x : E) ∈ d ∧ (x : E) ∉ q)) ∨
      ((x : E) ∈ s true ∧ ¬ ((x : E) ∈ d ∧ (x : E) ∉ q)) ↔ _
    rw [hUs false x,hUs true x,(hUport x).1,(hUport x).2]
    rfl
  have hGouterMem (x : ((prism (-1) 0 ∪ prism 0 1) \ ⋃ j : J, c j \ t j : Set P3)) :
      (x : P3) ∈ (S false \ (endDisk 0 \ endRim 0)) ∪
        (S true \ (endDisk 0 \ endRim 0)) ↔ (G x : V4) ∈ seam := by
    constructor
    · intro hx
      exact hGouter.subset ⟨x,hx,rfl⟩
    · intro hx
      obtain ⟨y,hy,hyx⟩ := hGouter.symm.subset hx
      have hyx' : y = x := G.injective (Subtype.ext hyx)
      exact hyx' ▸ hy
  have hFouter (x : (R false ∪ R true : Set E)) :
      (x : E) ∈ outer ↔ (F x : V4) ∈ seam :=
    (hUouter x).trans (hGouterMem (U' x))
  have hFcopy := hF
  obtain ⟨_,⟨L,hL,hLs,_⟩,_⟩ := hFcopy
  refine ⟨(fun j => g '' c j),(fun j => g '' t j),hgball,hgin,hgout,hgdis,
    L,F,hL,hLs,hF,hFmem,?_,hFouter,?_⟩
  · intro j
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hFmem j x).mp hx
    · intro y hy
      have htT : g '' t j ⊆ sphere \ ((upper \ seam) ∪ ⋃ j, (g '' c j) \ (g '' t j)) := by
        rw [← hGimage j]
        exact image_subset_iff.mpr fun x _ => (G x).property
      let x := F.symm ⟨y,htT hy⟩
      have heq : (F x : V4) = y := congrArg Subtype.val (F.apply_symm_apply _)
      exact ⟨x,(hFmem j x).mpr (heq.symm ▸ hy),heq⟩
  · apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hFouter x).mp hx
    · intro y hy
      have hsT : seam ⊆ sphere \ ((upper \ seam) ∪ ⋃ j, (g '' c j) \ (g '' t j)) := by
        exact hGouter.symm.subset.trans (image_subset_iff.mpr fun x _ => (G x).property)
      let x := F.symm ⟨y,hsT hy⟩
      have heq : (F x : V4) = y := congrArg Subtype.val (F.apply_symm_apply _)
      exact ⟨x,(hFouter x).mpr (heq.symm ▸ hy),heq⟩

end Set
