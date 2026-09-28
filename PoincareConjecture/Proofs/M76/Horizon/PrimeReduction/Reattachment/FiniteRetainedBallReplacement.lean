import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RetainedBallReplacement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SeparatedSphereCaps
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem compact_of_unit_ball_pair
    {X : Type*} [TopologicalSpace X] {Q S : Set X}
    (hQ : IsUnitBallPair V3 Q S) : IsCompact Q := by
  obtain ⟨_,H,_⟩ := hQ
  let : CompactSpace (closedBall (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact isCompact_iff_compactSpace.mpr H.symm.compactSpace

theorem exists_disjoint_compact_union_homeomorph
    {X Y κ : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] [Finite κ]
    (Q : κ → Set X) (C : κ → Set Y) (hQ : ∀ i, IsCompact (Q i))
    (hdisQ : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hdisC : Pairwise fun i j => Disjoint (C i) (C j))
    (e : ∀ i, Q i ≃ₜ C i) :
    ∃ H : (⋃ i, Q i) ≃ₜ (⋃ i, C i),
      ∀ i (x : Q i), (H ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : Y) = e i x := by
  classical
  let F : (⋃ i, Q i) → (⋃ i, C i) := fun x =>
    let i := (mem_iUnion.mp x.property).choose
    let y := e i ⟨x,(mem_iUnion.mp x.property).choose_spec⟩
    ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩
  have hF (i : κ) (x : Q i) :
      (F ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : Y) = e i x := by
    let hx : (x : X) ∈ ⋃ i, Q i := mem_iUnion.mpr ⟨i,x.property⟩
    have hi : (mem_iUnion.mp hx).choose = i := by
      by_contra hn
      exact disjoint_left.mp (hdisQ hn) (mem_iUnion.mp hx).choose_spec x.property
    change (e (mem_iUnion.mp hx).choose ⟨x,(mem_iUnion.mp hx).choose_spec⟩ : Y) = e i x
    have hsame (k : κ) (hki : k = i) (hxk : (x : X) ∈ Q k) :
        (e k ⟨x,hxk⟩ : Y) = e i x := by
      subst k
      rfl
    exact hsame _ hi _
  let P : κ → Set (⋃ i, Q i) := fun i => (Subtype.val : (⋃ i, Q i) → X) ⁻¹' Q i
  have hPcov : ⋃ i, P i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i,hi⟩
  have hcont : Continuous F := by
    apply (locallyFinite_of_finite P).continuous hPcov
      (fun i => (hQ i).isClosed.preimage continuous_subtype_val)
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : P i =>
        (⟨e i ⟨x.val.val,x.property⟩,
          mem_iUnion.mpr ⟨i,(e i ⟨x.val.val,x.property⟩).property⟩⟩ : (⋃ j, C j))) := by
      fun_prop
    convert hc using 1
    funext x
    exact Subtype.ext (hF i ⟨x.val.val,x.property⟩)
  have hinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨i,hxi⟩ := mem_iUnion.mp x.property
    obtain ⟨j,hyj⟩ := mem_iUnion.mp y.property
    have heq := congrArg Subtype.val hxy
    rw [hF i ⟨x,hxi⟩,hF j ⟨y,hyj⟩] at heq
    have hij : i = j := by
      by_contra hn
      exact disjoint_left.mp (hdisC hn) (e i ⟨x,hxi⟩).property
        (heq.symm ▸ (e j ⟨y,hyj⟩).property)
    subst j
    exact Subtype.ext (congrArg (fun z : Q i => (z : X))
      ((e i).injective (Subtype.ext heq)))
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨i,hyi⟩ := mem_iUnion.mp y.property
    refine ⟨⟨(e i).symm ⟨y,hyi⟩,mem_iUnion.mpr ⟨i,((e i).symm ⟨y,hyi⟩).property⟩⟩,?_⟩
    apply Subtype.ext
    rw [hF]
    exact congrArg Subtype.val ((e i).apply_symm_apply ⟨y,hyi⟩)
  let : CompactSpace (⋃ i, Q i) := isCompact_iff_compactSpace.mp (isCompact_iUnion hQ)
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective F ⟨hinj,hsurj⟩) hcont,hF⟩

theorem exists_finite_retained_ball_replacement
    {X Y κ : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] [Finite κ]
    {A : Set X} {A' : Set Y} (Q S : κ → Set X) (C T : κ → Set Y)
    (hA : IsClosed A) (hA' : IsClosed A')
    (hQ : ∀ i, IsUnitBallPair V3 (Q i) (S i))
    (hC : ∀ i, IsUnitBallPair V3 (C i) (T i))
    (hdisQ : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hdisC : Pairwise fun i j => Disjoint (C i) (C j))
    (hSQ : ∀ i, A ∩ Q i = S i) (hTC : ∀ i, A' ∩ C i = T i)
    (H : A ≃ₜ A') (hmark : ∀ i (x : A), (x : X) ∈ S i ↔ (H x : Y) ∈ T i) :
    ∃ G : (A ∪ ⋃ i, Q i : Set X) ≃ₜ (A' ∪ ⋃ i, C i : Set Y),
      (∀ x : A, (G ⟨x,Or.inl x.property⟩ : Y) = H x) ∧
      (∀ y : A', (G.symm ⟨y,Or.inl y.property⟩ : X) = H.symm y) ∧
      ∀ i (x : (A ∪ ⋃ i, Q i : Set X)), (x : X) ∈ Q i ↔ (G x : Y) ∈ C i := by
  classical
  have hSA (i : κ) : S i ⊆ A := (hSQ i).symm.subset.trans inter_subset_left
  have hTA (i : κ) : T i ⊆ A' := (hTC i).symm.subset.trans inter_subset_left
  let HB : ∀ i, S i ≃ₜ T i := fun i => H.restrictSubsets (hSA i) (hTA i) (hmark i)
  choose F hF hFmark using fun i => (hQ i).exists_extension (hC i) (HB i)
  obtain ⟨K,hK⟩ := exists_disjoint_compact_union_homeomorph Q C
    (fun i => compact_of_unit_ball_pair (hQ i)) hdisQ hdisC F
  have hoverlap (x : A) : (x : X) ∈ ⋃ i, Q i ↔ (H x : Y) ∈ ⋃ i, C i := by
    simp only [mem_iUnion]
    apply exists_congr
    intro i
    calc
      _ ↔ (x : X) ∈ S i := by rw [← hSQ i]; exact (and_iff_right x.property).symm
      _ ↔ (H x : Y) ∈ T i := hmark i x
      _ ↔ (H x : Y) ∈ C i := by rw [← hTC i]; exact and_iff_right (H x).property
  have hagree (x : X) (hxA : x ∈ A) (hxQ : x ∈ ⋃ i, Q i) :
      (H ⟨x,hxA⟩ : Y) = K ⟨x,hxQ⟩ := by
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hxQ
    rw [hK i ⟨x,hxi⟩]
    exact (congrArg Subtype.val (hF i ⟨x,(hSQ i).subset ⟨hxA,hxi⟩⟩)).symm
  obtain ⟨G,hGA,hGK⟩ := exists_closed_union_homeomorph hA
    (isCompact_iUnion (fun i => compact_of_unit_ball_pair (hQ i))).isClosed hA'
    (isCompact_iUnion (fun i => compact_of_unit_ball_pair (hC i))).isClosed
    H K hoverlap hagree
  have hGFi (i : κ) (x : Q i) :
      (G ⟨x,Or.inr (mem_iUnion.mpr ⟨i,x.property⟩)⟩ : Y) = F i x :=
    (hGK ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩).trans (hK i x)
  refine ⟨G,hGA,?_,?_⟩
  · intro y
    have hg : G ⟨H.symm y,Or.inl (H.symm y).property⟩ = ⟨y,Or.inl y.property⟩ := by
      apply Subtype.ext
      rw [hGA]
      exact congrArg Subtype.val (H.apply_symm_apply y)
    exact congrArg Subtype.val (G.injective ((G.apply_symm_apply _).trans hg.symm))
  · intro i x
    constructor
    · intro hx
      rw [hGFi i ⟨x,hx⟩]
      exact (F i ⟨x,hx⟩).property
    · intro hx
      let y := (F i).symm ⟨G x,hx⟩
      have heq : G ⟨y,Or.inr (mem_iUnion.mpr ⟨i,y.property⟩)⟩ = G x := by
        apply Subtype.ext
        rw [hGFi]
        exact congrArg Subtype.val ((F i).apply_symm_apply ⟨G x,hx⟩)
      exact (congrArg Subtype.val (G.injective heq)) ▸ y.property

open Geometry.SeparatedSphereCaps in
theorem exists_finite_retained_cone_replacement
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {A : Set X} (Q S : κ → Set X)
    (s : ∀ i, ChartwisePLSphere e (S i)) (hA : IsCompact A)
    (hball : ∀ i, IsUnitBallPair V3 (Q i) (S i))
    (hdisQ : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hcontact : ∀ i, A ∩ Q i = S i)
    (phi : X → E) (hphi : Continuous phi) (hinj : InjOn phi A)
    (hPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) :
    let j : X → E × (κ → ℝ) := lift ∘ phi
    let C : κ → Set (E × (κ → ℝ)) := fun i => cap i (phi '' S i)
    (∀ i, IsFinitePLBallPair V3 (C i) (j '' S i)) ∧
      (∀ i, (j '' A) ∩ C i = j '' S i) ∧
      Pairwise (fun i k => Disjoint (C i) (C k)) ∧
      ∃ G : (A ∪ ⋃ i, Q i : Set X) ≃ₜ (j '' A ∪ ⋃ i, C i : Set (E × (κ → ℝ))),
        (∀ x : A, (G ⟨x,Or.inl x.property⟩ : E × (κ → ℝ)) = j x) ∧
        (∀ x : A, (G.symm ⟨j x,Or.inl (mem_image_of_mem j x.property)⟩ : X) = x) ∧
        ∀ i (x : (A ∪ ⋃ i, Q i : Set X)),
          (x : X) ∈ Q i ↔ (G x : E × (κ → ℝ)) ∈ C i := by
  classical
  let j : X → E × (κ → ℝ) := lift ∘ phi
  let C : κ → Set (E × (κ → ℝ)) := fun i => cap i (phi '' S i)
  have hSA (i : κ) : S i ⊆ A := (hcontact i).symm.subset.trans inter_subset_left
  have hj : Continuous j := hphi.prodMk continuous_const
  have hji : InjOn j A := fun x hx y hy hxy => hinj hx hy (congrArg Prod.fst hxy)
  have hcap (i : κ) : IsFinitePLBallPair V3 (C i) (j '' S i) := by
    obtain ⟨P,hP,_⟩ := (s i).exists_finitePL_model_parametrization phi hPL
      (hinj.mono (hSA i)) rfl
    have hsphere : sphere (0 : V3) 1 = frontier (closedBall (0 : V3) 1) :=
      (frontier_closedBall _ one_ne_zero).symm
    have hne : (phi '' S i).Nonempty := by
      obtain ⟨x,hx⟩ := NormedSpace.sphere_nonempty (E := V3) (x := 0) |>.mpr
        (show (0 : ℝ) ≤ 1 by norm_num)
      exact ⟨P ⟨x,hx⟩,(P ⟨x,hx⟩).property⟩
    have h := isFinitePLBallPair_cap i (hP.symm.setCongr rfl hsphere) hne
      (isCompact_closedBall _ _) (convex_closedBall _ _)
      ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
    simpa only [C,j,image_image,Function.comp_def] using h
  have hcapTop (i : κ) : IsUnitBallPair V3 (C i) (j '' S i) := by
    obtain ⟨HB,_,hHB⟩ := (hcap i).exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
    exact ⟨(hcap i).1,HB,by simpa only [frontier_closedBall _ one_ne_zero] using hHB⟩
  have hcapContact (i : κ) : (j '' A) ∩ C i = j '' S i := by
    simpa only [j,C,image_image,Function.comp_def,inter_comm] using
      cap_inter_lift i (image_mono (hSA i) (f := phi))
  have hcapDis : Pairwise fun i k => Disjoint (C i) (C k) := by
    intro i k hik
    apply disjoint_caps hik
    apply disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy := hinj (hSA i hx) (hSA k hy) (hxz.trans hyz.symm)
    exact disjoint_left.mp (hdisQ hik) ((hball i).1 hx) (hxy ▸ (hball k).1 hy)
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let H : A ≃ₜ j '' A := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn j A hji) (hj.comp continuous_subtype_val |>.subtype_mk _)
  have hHval (x : A) : (H x : E × (κ → ℝ)) = j x := rfl
  have hmark (i : κ) (x : A) : (x : X) ∈ S i ↔ (H x : E × (κ → ℝ)) ∈ j '' S i := by
    rw [hHval]
    constructor
    · exact mem_image_of_mem j
    · rintro ⟨y,hy,heq⟩
      exact hji (hSA i hy) x.property heq ▸ hy
  obtain ⟨G,hGA,_,hGQ⟩ := exists_finite_retained_ball_replacement
    Q S C (fun i => j '' S i) hA.isClosed (hA.image hj).isClosed
    hball hcapTop hdisQ hcapDis hcontact hcapContact H hmark
  have hGj (x : A) : (G ⟨x,Or.inl x.property⟩ : E × (κ → ℝ)) = j x :=
    (hGA x).trans (hHval x)
  refine ⟨hcap,hcapContact,hcapDis,G,hGj,?_,hGQ⟩
  intro x
  have heq : G ⟨x,Or.inl x.property⟩ =
      ⟨j x,Or.inl (mem_image_of_mem j x.property)⟩ := Subtype.ext (hGj x)
  exact congrArg Subtype.val (G.injective ((G.apply_symm_apply _).trans heq.symm))

end PoincareConjecture.M76
