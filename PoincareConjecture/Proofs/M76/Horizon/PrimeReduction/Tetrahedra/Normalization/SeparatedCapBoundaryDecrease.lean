import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.SelectedBoundaryExcess
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.BoundaryComponentTransport
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem bool_finTwo_bijective_of_ne
    (side : Bool → Fin 2) (hne : side false ≠ side true) : Function.Bijective side := by
  constructor
  · intro a b hab
    cases a <;> cases b
    · rfl
    · exact (hne hab).elim
    · exact (hne hab.symm).elim
    · rfl
  · intro a
    by_cases h : a = side false
    · exact ⟨false,h.symm⟩
    refine ⟨true,?_⟩
    have hn : (side false).val ≠ (side true).val := fun h => hne (Fin.ext h)
    have ha : a.val ≠ (side false).val := fun ha => h (Fin.ext ha)
    apply Fin.ext
    omega

theorem OriginalDiskProduct.separated_cap_family_pairwise_disjoint
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (S : κ → Set X) (i : κ)
    (hS : Pairwise fun a b => Disjoint (S a) (S b))
    (ret : Bool → Set X) (hret : ∀ b, ret b ⊆ S i)
    (hretDis : Disjoint (ret true) (ret false))
    (hcontact : ∀ b, ret b ∩ P.closedStrip = P.capRimSet b)
    (havoid : MapsTo P.map (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1)
      (⋃ k : {k : κ // k ≠ i}, S k.val)ᶜ) :
    Pairwise fun a b : ({k : κ // k ≠ i} ⊕ Bool) =>
      Disjoint (Sum.elim (fun k : {k : κ // k ≠ i} => S k.val)
        (fun b => ret b ∪ P.capDisk b) a)
        (Sum.elim (fun k : {k : κ // k ≠ i} => S k.val)
          (fun b => ret b ∪ P.capDisk b) b) := by
  have hcapstrip (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply Subset.trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hcapDis : Disjoint (P.capDisk true) (P.capDisk false) := P.disjoint_capDisks true
  have hretcap (b : Bool) : Disjoint (ret b) (P.capDisk (!b)) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp (P.disjoint_capDisks b)
      (P.capRimSet_subset_capDisk b ((hcontact b).subset ⟨hx,hcapstrip (!b) hy⟩)) hy
  have hnewDis : Disjoint (ret true ∪ P.capDisk true) (ret false ∪ P.capDisk false) :=
    disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hretDis,hretcap true⟩,
      disjoint_union_right.mpr ⟨(hretcap false).symm,hcapDis⟩⟩
  have hother (a : {k : κ // k ≠ i}) (b : Bool) :
      Disjoint (S a.val) (ret b ∪ P.capDisk b) := by
    apply disjoint_union_right.mpr
    refine ⟨(hS a.property).mono_right (hret b),?_⟩
    apply disjoint_left.mpr
    rintro x hx ⟨z,hz,rfl⟩
    exact havoid (OriginalDiskProduct.cap_source_subset b hz) (mem_iUnion.mpr ⟨a,hx⟩)
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hS (fun h => hab (congrArg Sum.inl (Subtype.ext h)))
    | inr b => exact hother a b
  | inr a =>
    cases b with
    | inl b => exact (hother b a).symm
    | inr b =>
      cases a <;> cases b
      · exact (hab rfl).elim
      · exact hnewDis.symm
      · exact hnewDis
      · exact (hab rfl).elim

theorem OriginalDiskProduct.selected_separated_cap_boundary_excess_lt
    {X E ι κ ρ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ] [Finite ρ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {T : Set E} (hTK : T ⊆ K.space) {F : Set X}
    (hFT : F ⊆ g '' T) (hFout : Disjoint F (interior (g '' T)))
    (S : κ → Set X) (i : κ) (hSclosed : ∀ k, IsClosed (S k))
    (hSdis : Pairwise fun a b => Disjoint (S a) (S b))
    (hSK : ∀ k, S k ⊆ g '' K.space)
    (V : Fin 2 → Set X)
    (ret : Bool → Set X) (hret : ∀ b, ret b ⊆ S i)
    (hretDis : Disjoint (ret true) (ret false))
    (hcontact : ∀ b, ret b ∩ P.closedStrip = P.capRimSet b)
    (caps : ∀ b, ChartwisePLSphere e (ret b ∪ P.capDisk b))
    (hPint : MapsTo P.map (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1) (interior (g '' T)))
    (hPavoid : MapsTo P.map (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1)
      (⋃ k : {k : κ // k ≠ i}, S k.val)ᶜ)
    (side : Bool → Fin 2) (hside : side false ≠ side true)
    (htransport : ∀ b : Bool,
      let raw := V (side b) ∪ (j '' closedBall (0 : V2) 1)
      let separated := ret b ∪ P.capDisk b
      let A := K.space ∩ g ⁻¹' raw
      let B := K.space ∩ g ⁻¹' separated
      g '' A = raw ∧ g '' B = separated ∧
        ∃ h : E → E, EqOn h id (A \ g ⁻¹' interior (g '' T)) ∧
          ∃ G : (A ∩ T : Set E) ≃ₜ (B ∩ T : Set E),
            ∀ x : (A ∩ T : Set E), (G x : E) = h x)
    (rim : ρ → Set X) (rimSide : ρ → ({k : κ // k ≠ i} ⊕ Fin 2)) (point : ρ → X)
    (hrimclosed : ∀ a, IsClosed (rim a)) (hrimconn : ∀ a, IsConnected (rim a))
    (hrimdis : Pairwise fun a b => Disjoint (rim a) (rim b))
    (hrimcover : (⋃ a, rim a) = (⋃ k, S k) ∩ F)
    (hrimside : ∀ a, rim a ⊆ Sum.elim (fun k : {k : κ // k ≠ i} => S k.val) V (rimSide a))
    (hpoint : ∀ a, point a ∈ rim a)
    (hrawcount : ∀ selected : Set ({k : κ // k ≠ i} ⊕ Fin 2),
      let raw := Sum.elim (fun k : {k : κ // k ≠ i} => S k.val)
        (fun a => V a ∪ (j '' closedBall (0 : V2) 1))
      {a | rimSide a ∈ selected}.ncard -
        ((fun a => (rimSide a,connectedComponentIn (raw (rimSide a) ∩ (g '' T)) (point a))) ''
          {a | rimSide a ∈ selected}).ncard < boundaryComponentExcess (⋃ k, S k) (g '' T) F) :
    ∀ selected : Set ({k : κ // k ≠ i} ⊕ Bool),
      boundaryComponentExcess
        (⋃ a ∈ selected, Sum.elim (fun k : {k : κ // k ≠ i} => S k.val)
          (fun b => ret b ∪ P.capDisk b) a) (g '' T) F <
        boundaryComponentExcess (⋃ k, S k) (g '' T) F := by
  classical
  let τ : ({k : κ // k ≠ i} ⊕ Bool) ≃ ({k : κ // k ≠ i} ⊕ Fin 2) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.ofBijective side (bool_finTwo_bijective_of_ne side hside))
  let newSide := fun a => τ.symm (rimSide a)
  let rawOld := Sum.elim (fun k : {k : κ // k ≠ i} => S k.val)
    (fun a => V a ∪ (j '' closedBall (0 : V2) 1))
  let raw := Sum.elim (fun k : {k : κ // k ≠ i} => S k.val)
    (fun b => V (side b) ∪ (j '' closedBall (0 : V2) 1))
  let separated := Sum.elim (fun k : {k : κ // k ≠ i} => S k.val)
    (fun b => ret b ∪ P.capDisk b)
  let A := fun a => K.space ∩ g ⁻¹' raw a
  let B := fun a => K.space ∩ g ⁻¹' separated a
  have hrawτ (a) : raw a = rawOld (τ a) := by cases a <;> rfl
  have hrawSide (a : ρ) : raw (newSide a) = rawOld (rimSide a) := by
    rw [hrawτ]
    exact congrArg rawOld (τ.apply_symm_apply _)
  have hpointF (a : ρ) : rim a ⊆ F :=
    ((subset_iUnion rim a).trans hrimcover.subset).trans inter_subset_right
  have hrimRaw (a : ρ) : rim a ⊆ raw (newSide a) := by
    rw [hrawSide]
    intro x hx
    have h := hrimside a hx
    cases hsa : rimSide a with
    | inl k => simpa only [hsa,Sum.elim_inl,rawOld] using h
    | inr b => exact Or.inl (by simpa only [hsa,Sum.elim_inr] using h)
  have hAimage (a) : g '' A a = raw a := by
    cases a with
    | inl k =>
      change g '' (K.space ∩ g ⁻¹' S k.val) = S k.val
      rw [image_inter_preimage,inter_eq_right.mpr (hSK k.val)]
    | inr b => exact (htransport b).1
  have hBimage (a) : g '' B a = separated a := by
    cases a with
    | inl k =>
      change g '' (K.space ∩ g ⁻¹' S k.val) = S k.val
      rw [image_inter_preimage,inter_eq_right.mpr (hSK k.val)]
    | inr b => exact (htransport b).2.1
  choose f hf G hG using fun b => (htransport b).2.2
  let maps := Sum.elim (fun _ : {k : κ // k ≠ i} => id) f
  let H : ∀ a, (A a ∩ T : Set E) ≃ₜ (B a ∩ T : Set E) := fun a => by
    cases a with
    | inl k => exact Homeomorph.refl _
    | inr b => exact G b
  have hH (a) (x : (A a ∩ T : Set E)) : (H a x : E) = maps a x := by
    cases a with
    | inl k => rfl
    | inr b => exact hG b x
  have hmaps (a) : EqOn (maps a) id (A a \ g ⁻¹' interior (g '' T)) := by
    cases a with
    | inl k => exact fun _ _ => rfl
    | inr b => exact hf b
  have hboundaryForward (a) : raw a ∩ F ⊆ separated a := by
    rintro x ⟨hx,hxF⟩
    obtain ⟨z,hz,hzx⟩ := (hAimage a).symm.subset hx
    obtain ⟨w,hw,hwx⟩ := hFT hxF
    have hzw : z = w := hgi hz.1 (hTK hw) (hzx.trans hwx.symm)
    have hzT : z ∈ T := hzw.symm ▸ hw
    have hfix : maps a z = z := hmaps a ⟨hz,fun hn => disjoint_left.mp hFout hxF (hzx ▸ hn)⟩
    have hzB := (H a ⟨z,hz,hzT⟩).property.1
    rw [hH,hfix] at hzB
    exact (hBimage a).subset ⟨z,hzB,hzx⟩
  have hnewRim (a : ρ) : rim a ⊆ separated (newSide a) ∩ F := fun x hx =>
    ⟨hboundaryForward _ ⟨hrimRaw a hx,hpointF a hx⟩,hpointF a hx⟩
  have hnewCover : (⋃ a, rim a) = (⋃ a, separated a) ∩ F := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a,ha⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨newSide a,(hnewRim a ha).1⟩,(hnewRim a ha).2⟩
    · rintro x ⟨hx,hxF⟩
      obtain ⟨a,ha⟩ := mem_iUnion.mp hx
      apply hrimcover.symm.subset
      refine ⟨?_,hxF⟩
      cases a with
      | inl k => exact mem_iUnion.mpr ⟨k.val,ha⟩
      | inr b =>
        rcases ha with hretx | ⟨z,hz,hzx⟩
        · exact mem_iUnion.mpr ⟨i,hret b hretx⟩
        · exact (disjoint_left.mp hFout hxF
            (hzx ▸ hPint (OriginalDiskProduct.cap_source_subset b hz))).elim
  have hnewClosed (a) : IsClosed (separated a) := by
    cases a with
    | inl k => exact hSclosed k.val
    | inr b => exact (caps b).isCompact.isClosed
  have hnewDis : Pairwise fun a b => Disjoint (separated a) (separated b) :=
    P.separated_cap_family_pairwise_disjoint S i hSdis ret hret hretDis hcontact hPavoid
  intro selected
  let kept : Set ρ := {a | newSide a ∈ selected}
  have hcountTransport := boundary_component_label_ncard_eq_of_original_section_support
    K hK hg hgi A B (fun _ => inter_subset_left) (fun _ => inter_subset_left) hTK H maps hH hmaps
    newSide point
    (fun a => ⟨(hAimage _).symm.subset (hrimRaw a (hpoint a)),hFT (hpointF a (hpoint a))⟩)
    (fun a => fun hn => disjoint_left.mp hFout (hpointF a (hpoint a)) hn) selected
  simp only [hAimage,hBimage] at hcountTransport
  have hcanonical := boundaryComponentExcess_selected_eq_tagged_labels separated hnewClosed hnewDis hFT
    rim newSide point hrimclosed hrimconn hrimdis hnewRim hnewCover hpoint selected
  have hkept : {a | rimSide a ∈ τ '' selected} = kept := by
    ext a
    constructor
    · rintro ⟨b,hb,hba⟩
      change τ.symm (rimSide a) ∈ selected
      rw [←hba,τ.symm_apply_apply]
      exact hb
    · intro ha
      exact ⟨newSide a,ha,τ.apply_symm_apply _⟩
  let rawLabel := fun a => (newSide a,connectedComponentIn (raw (newSide a) ∩ (g '' T)) (point a))
  let oldLabel := fun a => (rimSide a,connectedComponentIn (rawOld (rimSide a) ∩ (g '' T)) (point a))
  let changeSide : ({k : κ // k ≠ i} ⊕ Bool) × Set X → ({k : κ // k ≠ i} ⊕ Fin 2) × Set X :=
    fun z => (τ z.1,z.2)
  have hchangeInj : Function.Injective changeSide := by
    intro x y hxy
    have hs : x.1 = y.1 := τ.injective (congrArg Prod.fst hxy)
    have hc : x.2 = y.2 := congrArg
      (fun z : ({k : κ // k ≠ i} ⊕ Fin 2) × Set X => z.2) hxy
    exact Prod.ext hs hc
  have hchange (a : ρ) : changeSide (rawLabel a) = oldLabel a := by
    apply Prod.ext (τ.apply_symm_apply _)
    exact congrArg (fun U => connectedComponentIn (U ∩ (g '' T)) (point a)) (hrawSide a)
  have hlabelCount : (oldLabel '' kept).ncard = (rawLabel '' kept).ncard := by
    have h := ncard_image_of_injective (rawLabel '' kept) hchangeInj
    rw [←image_comp,show changeSide ∘ rawLabel = oldLabel from funext hchange] at h
    exact h
  have hstrict := hrawcount (τ '' selected)
  dsimp only at hstrict
  rw [hkept] at hstrict
  change kept.ncard - (oldLabel '' kept).ncard < _ at hstrict
  rw [hlabelCount] at hstrict
  rw [hcanonical,←hcountTransport]
  exact hstrict

end PoincareConjecture.M76
