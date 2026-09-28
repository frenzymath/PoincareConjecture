import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.DiskBoundaryHomotopy

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76

theorem no_frontier_extension_of_disk_image_subset
    {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
    {D q : Set E} {B r : Set F} {R : Set X} {f : E → X} {g : F → X}
    (hq : q ⊆ D) (hr : r ⊆ B) (hf : ContinuousOn f D)
    (hg : IsEmbedding (fun x : B => g x))
    (himage : f '' D ⊆ g '' B)
    (hfq : ∀ x ∈ q, f x ∈ frontier R)
    (hgr : ∀ x ∈ B, g x ∈ frontier R ↔ x ∈ r)
    (hne : ¬ ∃ G : C(D,frontier R),
      ∀ x : q, (G ⟨x,hq x.property⟩ : X) = f x) :
    ¬ ∃ G : C(B,frontier R),
      ∀ x : r, (G ⟨x,hr x.property⟩ : X) = g x := by
  let v : C(D, Set.range (fun x : B => g x)) := ⟨fun x =>
    ⟨f x, by
      obtain ⟨y,hy,heq⟩ := himage ⟨x,x.property,rfl⟩
      exact ⟨⟨y,hy⟩,heq⟩⟩, by
        apply Continuous.subtype_mk
        exact hf.domRestrict⟩
  let H : C(D,B) := (⟨hg.toHomeomorph.symm,hg.toHomeomorph.symm.continuous⟩ :
    C(Set.range (fun x : B => g x),B)).comp v
  have hH (x : D) : g (H x) = f x := by
    exact congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply (v x))
  rintro ⟨G,hG⟩
  refine hne ⟨G.comp H,?_⟩
  intro x
  let y : r := ⟨H ⟨x,hq x.property⟩,
    (hgr _ (H ⟨x,hq x.property⟩).property).mp
      ((hH ⟨x,hq x.property⟩).symm ▸ hfq x x.property)⟩
  exact (hG y).trans (hH ⟨x,hq x.property⟩)

theorem no_frontier_extension_of_physical_disk_homotopy
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace F] [TopologicalSpace X] [T2Space X]
    {D q : Set E} {B r : Set F} {Y R : Set X} {f : F → X} {v : E → X}
    (hD : IsFinitePLBallPair (ℝ × ℝ) D q) (hr : r ⊆ B)
    (hf : ContinuousOn f B) (hfq : ∀ x ∈ r,f x ∈ frontier R)
    (hv : ContinuousOn v D) (hvi : Set.InjOn v D) (hvimage : v '' D = Y)
    (hvproper : ∀ x ∈ D,v x ∈ frontier R ↔ x ∈ q)
    (H : C(↥(Icc (0 : ℝ) 1) × ↥Y,X))
    (hH1 : ∀ z : Y,H (⟨1,by norm_num⟩,z) = z)
    (hHfront : ∀ z,H z ∈ frontier R ↔ (z.2:X) ∈ frontier R)
    (hHi : Function.Injective (fun z : Y => H (⟨0,by norm_num⟩,z)))
    (himage : f '' B ⊆ Set.range (fun z : Y => H (⟨0,by norm_num⟩,z)))
    (hne : ¬ ∃ G : C(B,frontier R),∀ x : r,(G ⟨x,hr x.property⟩ : X) = f x) :
    ¬ ∃ G : C(D,frontier R),∀ x : q,(G ⟨x,hD.1 x.property⟩ : X) = v x := by
  classical
  let j : C(D,Y) := ⟨fun x => ⟨v x,hvimage.subset ⟨x,x.property,rfl⟩⟩,by
    apply Continuous.subtype_mk
    exact hv.domRestrict⟩
  have hji : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (hvi x.property y.property (congrArg Subtype.val hxy))
  have hjs : Function.Surjective j := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hvimage.superset y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  let G : C(↥(Icc (0 : ℝ) 1) × ↥D,X) := H.comp ⟨fun z => (z.1,j z.2),by fun_prop⟩
  let k : E → X := fun x => if hx : x ∈ D then G (⟨0,by norm_num⟩,⟨x,hx⟩) else v x
  have hkval (x : D) : k x = G (⟨0,by norm_num⟩,x) := dif_pos x.property
  have hkc : Continuous (fun x : D => k x) := by
    have hc : Continuous (fun x : D => G (⟨0,by norm_num⟩,x)) := by fun_prop
    exact hc.congr (fun x => (hkval x).symm)
  have hki : Function.Injective (fun x : D => k x) := by
    intro x y hxy
    change k x = k y at hxy
    rw [hkval x,hkval y] at hxy
    exact hji (hHi hxy)
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  have hkemb := (hkc.isClosedEmbedding hki).isEmbedding
  have hkimage : f '' B ⊆ k '' D := by
    intro x hx
    obtain ⟨z,hz⟩ := himage hx
    obtain ⟨y,hy⟩ := hjs z
    refine ⟨y,y.property,?_⟩
    rw [hkval]
    change H (⟨0,by norm_num⟩,j y) = x
    rw [hy]
    exact hz
  have hkproper (x : E) (hx : x ∈ D) : k x ∈ frontier R ↔ x ∈ q := by
    rw [hkval ⟨x,hx⟩]
    exact (hHfront (⟨0,by norm_num⟩,j ⟨x,hx⟩)).trans (hvproper x hx)
  have hnk := no_frontier_extension_of_disk_image_subset hr hD.1 hf hkemb
    hkimage hfq hkproper hne
  have hk : ContinuousOn k D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hkc
  apply no_frontier_extension_of_marked_disk_homotopy hD
    hk hv
    (fun x hx => (hkproper x (hD.1 hx)).mpr hx) G
    (fun x => (hkval x).symm) (fun x => hH1 (j x)) ?_ hnk
  intro z
  exact (hHfront (z.1,j z.2)).trans ((hvproper z.2 z.2.property).trans
    (hkproper z.2 z.2.property).symm)

end PoincareConjecture.M76
