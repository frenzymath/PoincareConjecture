import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SelectedHoleDiskPortNormalization









set_option autoImplicit false

open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

open PoincareConjecture.M76.HamiltonIndexTwoStandard


theorem restrict_punctured_ball
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Finite ι]
    {B S : Set E} {T : Set F} (hB : IsFinitePLBallPair V3 B S)
    (a r : ι → Set E) (ha : ∀ j, IsFinitePLBallPair V3 (a j) (r j))
    (haB : ∀ j, a j ⊆ B \ S) (hdis : Pairwise fun j k => Disjoint (a j) (a k))
    (H : B ≃ₜ T) (hH : H.IsFinitePL) (f : E → F)
    (hf : FinitePiecewiseAffineOn f B) (hfi : InjOn f B)
    (hval : ∀ x : B, (H x : F) = f x) :
    let p := B \ ⋃ j, a j \ r j
    let Q := T \ ⋃ j, (f '' a j) \ (f '' r j)
    ∃ e : p ≃ₜ Q, e.IsFinitePL ∧ (∀ x : p, (e x : F) = f x) ∧
      ∀ j (x : p), (x : E) ∈ r j ↔ (e x : F) ∈ f '' r j := by
  dsimp only
  have hmarked (c : Set E) (hc : c ⊆ B) (x : B) :
      (x : E) ∈ c ↔ (H x : F) ∈ f '' c := by
    rw [hval]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hfi (hc hy) x.property hyx ▸ hy
  have hopen : IsOpen ((Subtype.val : B → E) ⁻¹' (⋃ j, a j \ r j)) := by
    rw [preimage_iUnion]
    exact isOpen_iUnion fun j => hB.isOpen_nested_ball_rim_complement
      (ha j) ((haB j).trans sdiff_subset)
  have himage : (Subtype.val : B → E) ''
      (((Subtype.val : B → E) ⁻¹' (⋃ j, a j \ r j))ᶜ) = B \ ⋃ j, a j \ r j := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hclosed : IsClosed (B \ ⋃ j, a j \ r j) := by
    rw [← himage]
    exact hB.isCompact.isClosed.isClosedMap_subtype_val _ hopen.isClosed_compl
  obtain ⟨K, hK, hKs, _⟩ := hf
  obtain ⟨_, L, _, _, _, _, _, hL, hLs, _, _⟩ :=
    K.exists_finite_closed_punctured_ball_carrier hK a r ha
      (fun j => (haB j).trans (sdiff_subset.trans hKs.symm.subset)) hdis
      (hKs.symm ▸ hclosed)
  have hLspace : L.space = B \ ⋃ j, a j \ r j := by simpa only [hKs] using hLs
  have hpuncture (x : B) : (x : E) ∈ B \ ⋃ j, a j \ r j ↔
      (H x : F) ∈ T \ ⋃ j, (f '' a j) \ (f '' r j) := by
    have hholes : (x : E) ∈ ⋃ j, a j \ r j ↔
        (H x : F) ∈ ⋃ j, (f '' a j) \ (f '' r j) := by
      simp only [mem_iUnion, mem_sdiff,
        ← hmarked (a _) ((haB _).trans sdiff_subset),
        ← hmarked (r _) ((ha _).1.trans ((haB _).trans sdiff_subset))]
    simp only [mem_sdiff, x.property, (H x).property, true_and, hholes]
  exact ⟨H.restrictSubsets sdiff_subset sdiff_subset hpuncture,
    hH.restrictSubsets sdiff_subset sdiff_subset hpuncture L hL hLspace,
    (fun x => hval ⟨x, x.property.1⟩),
    fun j x => hmarked (r j) ((ha j).1.trans ((haB j).trans sdiff_subset))
      ⟨x, x.property.1⟩⟩




theorem exists_selected_hole_disk_port_source_union {ι : Type*} [Finite ι]
    (a r : Bool → ι → Set V4)
    (ha : ∀ b j, IsFinitePLBallPair V3 (a b j) (r b j))
    (haS : ∀ b j, a b j ⊆ sphere)
    (hopen : ∀ b j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a b j \ r b j)))
    (hdis : ∀ b, Pairwise fun j k => Disjoint (a b j) (a b k)) (i : Bool → ι)
    {d q : Set V4} (hd : IsFinitePLBallPair P2 d q)
    (hdr : ∀ b, d ⊆ r b (i b)) (hout : ∀ b, (r b (i b) \ d).Nonempty)
    (hcontact : (sphere \ ⋃ j, a false j \ r false j) ∩
      (sphere \ ⋃ j, a true j \ r true j) = d) :
    let J := (b : Bool) × {j : ι // j ≠ i b}
    let p := (sphere \ ⋃ j, a false j \ r false j) ∪
      (sphere \ ⋃ j, a true j \ r true j)
    ∃ c t : J → Set V4,
      (∀ j, IsFinitePLBallPair V3 (c j) (t j)) ∧
      (∀ j, c j ⊆ lower \ seam) ∧ (∀ j, Disjoint upper (c j)) ∧
      Pairwise (fun j k => Disjoint (c j) (c k)) ∧
      ∃ (L : SimplicialComplex ℝ V4)
        (F : p ≃ₜ (sphere \ ((upper \ seam) ∪ ⋃ j, c j \ t j) : Set V4)),
        L.faces.Finite ∧ L.space = p ∧ F.IsFinitePL ∧
        (∀ j (x : p), (x : V4) ∈ r j.1 j.2 ↔ (F x : V4) ∈ t j) ∧
        ∀ j, (fun x : p => (F x : V4)) ''
          ((Subtype.val : p → V4) ⁻¹' r j.1 j.2) = t j := by
  dsimp only
  let B := fun b => sphere \ (a b (i b) \ r b (i b))
  let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
  let S := fun b : Bool => if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
    else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
  let J := (b : Bool) × {j : ι // j ≠ i b}
  let p := fun b => sphere \ ⋃ j, a b j \ r b j
  obtain ⟨f, H, hmaps, hagree, g, hgball, hgin, hgout, hgdis,
      _, G, _, _, hG, _, hGmem, hGimage⟩ :=
    exists_selected_hole_disk_port_sum a r ha haS hopen hdis i hd hdr hout
  let c : J → Set P3 := fun j => f j.1 '' a j.1 j.2
  let t : J → Set P3 := fun j => f j.1 '' r j.1 j.2
  let Q := fun b => P b \ ⋃ j : {j : ι // j ≠ i b}, (f b '' a b j) \ (f b '' r b j)
  have hB (b : Bool) := selected_hole_punctured_ball
    (a b) (r b) (ha b) (haS b) (hopen b) (hdis b) (i b)
  have hpB (b : Bool) : p b ⊆ B b := by
    dsimp only [p]
    rw [← (hB b).2.2.1]
    exact sdiff_subset
  have hex (b : Bool) : ∃ e : p b ≃ₜ Q b, e.IsFinitePL ∧
      (∀ x : p b, (e x : P3) = f b x) ∧
      ∀ j : {j : ι // j ≠ i b}, ∀ x : p b,
        (x : V4) ∈ r b j ↔ (e x : P3) ∈ f b '' r b j := by
    have hp := (hB b).2.2.1
    obtain ⟨e, he, hval, hmark⟩ := restrict_punctured_ball (hB b).1
      (fun j : {j : ι // j ≠ i b} => a b j) (fun j => r b j)
      (fun j => ha b j) (hB b).2.1
      (fun j k hjk => hdis b (Subtype.val_injective.ne hjk))
      (H b) (hmaps b).1 (f b) (hmaps b).2.1 (hmaps b).2.2.1 (hmaps b).2.2.2.1
    refine ⟨(Homeomorph.setCongr hp.symm).trans e, ?_, ?_, ?_⟩
    · exact he.setCongr hp rfl
    · exact fun x => hval ⟨x, hp.symm.subset x.property⟩
    · exact fun j x => hmark j ⟨x, hp.symm.subset x.property⟩
  choose e he hval hmark using hex
  have hPinter : P false ∩ P true = endDisk 0 := by
    ext x
    change ((x.1 ∈ CoordinateHalfBoxes.base 1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∧
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1)) ↔
      x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = 0
    constructor
    · intro hx
      exact ⟨hx.1.1, le_antisymm hx.1.2.2 hx.2.2.1⟩
    · rintro ⟨hx, heq⟩
      rw [heq]
      exact ⟨⟨hx, by norm_num⟩, hx, by norm_num⟩
  have hdP (b : Bool) : endDisk 0 ⊆ P b := by
    cases b
    · exact fun _ hx => (hPinter.symm.subset hx).1
    · exact fun _ hx => (hPinter.symm.subset hx).2
  have hdS (b : Bool) : endDisk 0 ⊆ S b := by
    cases b
    · exact subset_union_right
    · exact subset_union_right.trans subset_union_left
  have hhole (b : Bool) (j : {j : ι // j ≠ i b}) :
      f b '' a b j ⊆ P b \ S b := by
    rintro _ ⟨x, hx, rfl⟩
    have hj := (hB b).2.1 j hx
    have hv := (hmaps b).2.2.2.1 ⟨x, hj.1⟩
    refine ⟨hv ▸ (H b ⟨x, hj.1⟩).property, ?_⟩
    intro hs
    exact hj.2 (((hmaps b).2.2.2.2.1 _).mpr (hv.symm ▸ hs))
  have hdQ (b : Bool) : endDisk 0 ⊆ Q b := by
    intro x hx
    refine ⟨hdP b hx, ?_⟩
    intro hh
    obtain ⟨j, hj, _⟩ := mem_iUnion.mp hh
    exact (hhole b j hj).2 (hdS b hx)
  have hQinter : Q false ∩ Q true = endDisk 0 := by
    apply Subset.antisymm
    · exact fun _ hx => hPinter.subset ⟨hx.1.1, hx.2.1⟩
    · exact fun _ hx => ⟨hdQ false hx, hdQ true hx⟩
  have heport (b : Bool) (x : p b) : (x : V4) ∈ d ↔ (e b x : P3) ∈ endDisk 0 := by
    rw [hval]
    have h := (hmaps b).2.2.2.2.2 ⟨x, hpB b x.property⟩
    rwa [(hmaps b).2.2.2.1] at h
  have hoverlap (x : p false) : (x : V4) ∈ p true ↔ (e false x : P3) ∈ Q true := by
    constructor
    · intro hx
      exact hdQ true ((heport false x).mp (hcontact.subset ⟨x.property, hx⟩))
    · intro hx
      exact (hcontact.symm.subset ((heport false x).mpr
        (hQinter.subset ⟨(e false x).property, hx⟩))).2
  obtain ⟨E, hE, hEfalse, hEtrue⟩ := Homeomorph.exists_union_finitePL
    (e false) (e true) (he false) (he true) hoverlap
    (fun x hx hy => (hval false ⟨x, hx⟩).trans
      ((hagree (hcontact.subset ⟨hx, hy⟩)).trans (hval true ⟨x, hy⟩).symm))
  have hkeep (b : Bool) (x : p b) :
      (E ⟨x, by cases b; exact Or.inl x.property; exact Or.inr x.property⟩ : P3) = e b x := by
    cases b
    · exact hEfalse x
    · exact hEtrue x
  have hQunion : Q false ∪ Q true =
      (prism (-1) 0 ∪ prism 0 1) \ ⋃ j : J, c j \ t j := by
    have hc (b : Bool) (j : {j : ι // j ≠ i b}) :
        Disjoint (f b '' a b j) (P (!b)) := by
      apply disjoint_left.mpr
      intro x hx hy
      have hi : x ∈ endDisk 0 := by
        cases b
        · exact hPinter.subset ⟨(hhole false j hx).1, hy⟩
        · exact hPinter.subset ⟨hy, (hhole true j hx).1⟩
      exact (hhole b j hx).2 (hdS b hi)
    apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · refine ⟨Or.inl hx.1, ?_⟩
        intro hh
        obtain ⟨⟨b,j⟩, hj, hnr⟩ := mem_iUnion.mp hh
        cases b
        · exact hx.2 (mem_iUnion.mpr ⟨j, hj, hnr⟩)
        · exact disjoint_left.mp (hc true j) hj hx.1
      · refine ⟨Or.inr hx.1, ?_⟩
        intro hh
        obtain ⟨⟨b,j⟩, hj, hnr⟩ := mem_iUnion.mp hh
        cases b
        · exact disjoint_left.mp (hc false j) hj hx.1
        · exact hx.2 (mem_iUnion.mpr ⟨j, hj, hnr⟩)
    · intro x hx
      rcases hx.1 with hxf | hxt
      · refine Or.inl ⟨hxf, ?_⟩
        intro hh
        obtain ⟨j,hj⟩ := mem_iUnion.mp hh
        exact hx.2 (mem_iUnion.mpr ⟨⟨false,j⟩,hj⟩)
      · refine Or.inr ⟨hxt, ?_⟩
        intro hh
        obtain ⟨j,hj⟩ := mem_iUnion.mp hh
        exact hx.2 (mem_iUnion.mpr ⟨⟨true,j⟩,hj⟩)
  let E' := E.trans (Homeomorph.setCongr hQunion)
  have hE' : E'.IsFinitePL := hE.setCongr rfl hQunion
  let F := E'.trans G
  have hF : F.IsFinitePL := hE'.trans hG
  have hrp (b : Bool) (j : ι) : r b j ⊆ p b := (hB b).2.2.2 j
  have hrQ (j : J) : t j ⊆ Q j.1 := by
    rintro _ ⟨x,hx,rfl⟩
    rw [← hval j.1 ⟨x,hrp j.1 j.2 hx⟩]
    exact (e j.1 ⟨x,hrp j.1 j.2 hx⟩).property
  have hEmem (j : J) (x : (p false ∪ p true : Set V4)) :
      (x : V4) ∈ r j.1 j.2 ↔ (E x : P3) ∈ t j := by
    let er := (e j.1).restrictSubsets (hrp j.1 j.2) (hrQ j) (hmark j.1 j.2)
    have hpUnion (b : Bool) : p b ⊆ p false ∪ p true := by
      cases b
      · exact subset_union_left
      · exact subset_union_right
    have hQUnion (b : Bool) : Q b ⊆ Q false ∪ Q true := by
      cases b
      · exact subset_union_left
      · exact subset_union_right
    exact E.mem_subset_iff_of_extension er ((hrp j.1 j.2).trans (hpUnion j.1))
      ((hrQ j).trans (hQUnion j.1))
      (fun y => Subtype.ext (hkeep j.1 ⟨y,hrp j.1 j.2 y.property⟩)) x
  have hFmem (j : J) (x : (p false ∪ p true : Set V4)) :
      (x : V4) ∈ r j.1 j.2 ↔ (F x : V4) ∈ g '' t j :=
    (hEmem j x).trans (hGmem j (E' x))
  have hFcopy := hF
  obtain ⟨_, ⟨L,hL,hLs,_⟩,_⟩ := hFcopy
  refine ⟨(fun j => g '' c j), (fun j => g '' t j), hgball, hgin, hgout, hgdis,
    L, F, hL, hLs, hF, hFmem, ?_⟩
  intro j
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (hFmem j x).mp hx
  · intro y hy
    have htT : g '' t j ⊆ sphere \ ((upper \ seam) ∪ ⋃ j, (g '' c j) \ (g '' t j)) := by
      rw [← hGimage j]
      exact image_subset_iff.mpr fun x _ => (G x).property
    let x := F.symm ⟨y,htT hy⟩
    have heq : (F x : V4) = y := congrArg Subtype.val (F.apply_symm_apply _)
    exact ⟨x, (hFmem j x).mpr (heq.symm ▸ hy), heq⟩

end Set
