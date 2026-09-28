import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.InwardAnnulus










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

private theorem exists_annular_side_in_region
    {X : Type*} [TopologicalSpace X] {S R r : Set X}
    (core band : Fin 2 → Set X)
    (hcore : ∀ i, IsClosed (core i))
    (hcorer : ∀ i, Disjoint (core i) r)
    (hcover : (core 0 ∪ band 0) ∪ (core 1 ∪ band 1) = S)
    (hconn : ∀ i, IsConnected (band i \ r))
    (havoid : ∀ i, Disjoint (band i \ r) (frontier R))
    (hrfront : r ⊆ frontier R)
    (hacc : (r ∩ closure (S ∩ interior R)).Nonempty) :
    ∃ i, band i \ r ⊆ interior R := by
  obtain ⟨x,hxr,hxcl⟩ := hacc
  let U := (core 0 ∪ core 1)ᶜ
  have hU : IsOpen U := ((hcore 0).union (hcore 1)).isOpen_compl
  have hxU : x ∈ U := by
    rintro (hx | hx)
    · exact disjoint_left.mp (hcorer 0) hx hxr
    · exact disjoint_left.mp (hcorer 1) hx hxr
  obtain ⟨y,hyU,hyS,hyR⟩ := mem_closure_iff.mp hxcl U hU hxU
  have hyband : ∃ i, y ∈ band i := by
    rcases hcover.symm.subset hyS with (h | h) | (h | h)
    · exact (hyU (Or.inl h)).elim
    · exact ⟨0,h⟩
    · exact (hyU (Or.inr h)).elim
    · exact ⟨1,h⟩
  obtain ⟨i,hi⟩ := hyband
  exact ⟨i,(hconn i).isPreconnected.subset_interior_of_avoids_frontier (havoid i)
    ⟨y,⟨hi,fun hr => (hrfront hr).2 hyR⟩,hyR⟩⟩

theorem connected_piece_subset_of_one_sided_rim_neighborhood
    {X : Type*} [TopologicalSpace X] {S R A B r U P : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hR : IsClosed R)
    (hwhole : A ∪ B = S) (hinter : A ∩ B = r)
    (hU : IsOpen U) (hrU : r ⊆ U) (hside : (S ∩ R) ∩ U ⊆ A)
    (hP : IsPreconnected P) (hPS : P ⊆ S) (hPR : P ⊆ R)
    (hmeet : (P ∩ r).Nonempty) : P ⊆ A := by
  let T := (B ∩ R) ∩ Uᶜ
  have hT : IsClosed T := (hB.inter hR).inter hU.isClosed_compl
  have hcover : P ⊆ A ∪ T := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl (hside ⟨⟨hPS hx,hPR hx⟩,hxU⟩)
    · exact (hwhole.symm.subset (hPS hx)).elim Or.inl
        (fun hb => Or.inr ⟨⟨hb,hPR hx⟩,hxU⟩)
  have hdis : A ∩ T = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxA,⟨hxB,_⟩,hxU⟩
    exact hxU (hrU (hinter.subset ⟨hxA,hxB⟩))
  have hor := isPreconnected_iff_subset_of_disjoint_closed.mp hP A T hA hT hcover
    (by rw [hdis,inter_empty])
  rcases hor with h | h
  · exact h
  · obtain ⟨x,hxP,hxr⟩ := hmeet
    exact False.elim ((h hxP).2 (hrU hxr))

theorem ChartwisePLSphere.exists_two_sided_rim_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S R O : Set X}
    (s : ChartwisePLSphere e S) (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ i, IsFinitePLBallPair P2 (d i) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    (hR : IsClosed R) (hO : IsOpen O) (hrO : s.map '' r ⊆ O)
    (hrfront : s.map '' r ⊆ frontier R)
    (hisolate : (S ∩ O) ∩ frontier R ⊆ s.map '' r)
    (hinward : (s.map '' r ∩ closure (S ∩ interior R)).Nonempty)
    (houtward : (s.map '' r ∩ closure (S ∩ Rᶜ)).Nonempty) :
    ∃ (i : Fin 2) (U : Set X), IsOpen U ∧ s.map '' r ⊆ U ∧ U ⊆ O ∧
      (S ∩ R) ∩ U ⊆ s.map '' d i ∧
      (S ∩ Rᶜ) ∩ U ⊆ s.map '' d i.rev ∧
      ((s.map '' d i.rev) ∩ R) ∩ U ⊆ s.map '' r ∧
      ∀ P : Set X, IsPreconnected P → P ⊆ S → P ⊆ R →
        (P ∩ s.map '' r).Nonempty → P ⊆ s.map '' d i := by
  classical
  obtain ⟨a,f,k,q,b,hdata,_,_,_,_,hcover⟩ :=
    s.exists_separated_retained_circle_disks d hd hwhole hinter hO hrO
  choose ha ha1 hf hfi hfd hfr hk hq hb hkp hkb hkbi hkr hrb hbO hkPL hbPL hsf H hH hHval
    using hdata
  have hdS (i : Fin 2) : d i ⊆ Sphere := by
    fin_cases i
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hks (i) : k i ⊆ Sphere := (subset_union_left.trans (hkb i).subset).trans (hdS i)
  have hbs (i) : b i ⊆ Sphere := (subset_union_right.trans (hkb i).subset).trans (hdS i)
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hrS : r ⊆ Sphere := (hd 0).1.trans (hdS 0)
  have hmapS (x : V3) (hx : x ∈ Sphere) : s.map x ∈ S := by
    rw [s.map_eq ⟨x,hx⟩]
    exact (s.parametrization ⟨x,hx⟩).property
  have hbc (i) : IsConnected ((s.map '' b i) \ (s.map '' r)) := by
    have hc : IsConnected (b i \ r) := by
      rw [hb i,←hfr i]
      exact isConnected_retained_annulus_without_rim (ha i) (ha1 i)
        (hf i).continuousOn (hfi i)
    rw [←Set.InjOn.image_sdiff_subset (hsi.mono (hbs i)) (hrb i)]
    exact hc.image _ (s.piecewiseAffine.continuousOn.mono (sdiff_subset.trans (hbs i)))
  have hkc (i) : IsClosed (s.map '' k i) :=
    ((hkp i).isCompact.image_of_continuousOn (hkPL i).continuousOn).isClosed
  have hkdis (i) : Disjoint (s.map '' k i) (s.map '' r) := by
    apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
    exact disjoint_left.mp (hkr i) hx
      ((hsi (hrS hy) (hks i hx) hyx) ▸ hy)
  have hbfront (i) : Disjoint ((s.map '' b i) \ (s.map '' r)) (frontier R) := by
    apply disjoint_left.mpr
    rintro x ⟨⟨y,hy,rfl⟩,hnot⟩ hxfront
    exact hnot (hisolate ⟨⟨hmapS y (hbs i hy),hbO i ⟨y,hy,rfl⟩⟩,hxfront⟩)
  obtain ⟨i,hi⟩ := exists_annular_side_in_region
    (fun i => s.map '' k i) (fun i => s.map '' b i) hkc hkdis hcover hbc hbfront hrfront hinward
  obtain ⟨j,hj⟩ := exists_annular_side_in_region (R := Rᶜ)
    (fun i => s.map '' k i) (fun i => s.map '' b i) hkc hkdis hcover hbc
    (by simpa only [frontier_compl] using hbfront)
    (by simpa only [frontier_compl] using hrfront)
    (by simpa only [hR.isOpen_compl.interior_eq] using houtward)
  have hjout : (s.map '' b j) \ (s.map '' r) ⊆ Rᶜ := hj.trans interior_subset
  have hij : i ≠ j := by
    intro heq
    obtain ⟨x,hx⟩ := (hbc i).nonempty
    exact hjout (heq ▸ hx) (interior_subset (hi hx))
  have hji : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
  subst j
  let U := ((s.map '' k 0) ∪ (s.map '' k 1))ᶜ ∩ O
  have hU : IsOpen U := ((hkc 0).union (hkc 1)).isOpen_compl.inter hO
  have hUband (x : X) (hxS : x ∈ S) (hxU : x ∈ U) :
      x ∈ s.map '' b i ∨ x ∈ s.map '' b i.rev := by
    have h : x ∈ s.map '' b 0 ∨ x ∈ s.map '' b 1 := by
      rcases hcover.symm.subset hxS with (h | h) | (h | h)
      · exact (hxU.1 (Or.inl h)).elim
      · exact Or.inl h
      · exact (hxU.1 (Or.inr h)).elim
      · exact Or.inr h
    fin_cases i
    · simpa using h
    · simpa [or_comm] using h
  have hbdi (l) : s.map '' b l ⊆ s.map '' d l :=
    image_mono (subset_union_right.trans (hkb l).subset)
  have hdd : (s.map '' d i) ∩ (s.map '' d i.rev) = s.map '' r := by
    rw [←hsi.image_inter (hdS i) (hdS i.rev)]
    congr 1
    fin_cases i
    · exact hinter
    · exact (inter_comm _ _).trans hinter
  have hrU : s.map '' r ⊆ U := by
    intro x hx
    exact ⟨fun h => h.elim (fun hk => disjoint_left.mp (hkdis 0) hk hx)
      (fun hk => disjoint_left.mp (hkdis 1) hk hx),hrO hx⟩
  have hin : (S ∩ R) ∩ U ⊆ s.map '' d i := by
    rintro x ⟨⟨hxS,hxR⟩,hxU⟩
    rcases hUband x hxS hxU with hb | hb
    · exact hbdi i hb
    · by_cases hr : x ∈ s.map '' r
      · exact image_mono (hd i).1 hr
      · exact (hjout ⟨hb,hr⟩ hxR).elim
  refine ⟨i,U,hU,hrU,inter_subset_right,hin,?_,?_,?_⟩
  · rintro x ⟨⟨hxS,hxR⟩,hxU⟩
    rcases hUband x hxS hxU with hb | hb
    · by_cases hr : x ∈ s.map '' r
      · exact image_mono (hd i.rev).1 hr
      · exact (hxR (interior_subset (hi ⟨hb,hr⟩))).elim
    · exact hbdi i.rev hb
  · rintro x ⟨⟨hxother,hxR⟩,hxU⟩
    have hxS : x ∈ S := by
      obtain ⟨y,hy,rfl⟩ := hxother
      exact hmapS y (hdS i.rev hy)
    rcases hUband x hxS hxU with hb | hb
    · exact hdd.subset ⟨hbdi i hb,hxother⟩
    · by_cases hr : x ∈ s.map '' r
      · exact hr
      · exact (hjout ⟨hb,hr⟩ hxR).elim
  · intro P hP hPS hPR hmeet
    apply connected_piece_subset_of_one_sided_rim_neighborhood
      ((hd i).isCompact.image_of_continuousOn
        (s.piecewiseAffine.continuousOn.mono (hdS i))).isClosed
      ((hd i.rev).isCompact.image_of_continuousOn
        (s.piecewiseAffine.continuousOn.mono (hdS i.rev))).isClosed
      hR ?_ hdd hU hrU hin hP hPS hPR hmeet
    have hdi : d i ∪ d i.rev = Sphere := by
      fin_cases i
      · exact hwhole
      · exact (union_comm _ _).trans hwhole
    rw [←image_union,hdi]
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hmapS x hx
    · intro x hx
      refine ⟨s.parametrization.symm ⟨x,hx⟩,(s.parametrization.symm ⟨x,hx⟩).property,?_⟩
      rw [s.map_eq]
      exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨x,hx⟩)

end PoincareConjecture.M76
