import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.NormalArcOverlap
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem original_normal_arc_incidence
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] (K : SimplicialComplex ℝ E)
    (g : E → X) (hgi : InjOn g K.space) {S : Set X}
    (havoid : Disjoint S (g '' K.vertices))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (γ : {s : K.FaceOfCard 3 // s.1 ⊆ t} → Type*)
    (d r : ∀ s, γ s → Set E)
    (hdis : ∀ s, Pairwise fun i j => Disjoint (d s i) (d s j))
    (hphysical : ∀ s, g '' (⋃ i, d s i) = S ∩ (g '' convexHull ℝ (s.1.1 : Set E)))
    (hsub : ∀ s, (⋃ i, d s i) ⊆ convexHull ℝ (s.1.1 : Set E))
    (hrim : ∀ s i, r s i = d s i ∩ intrinsicFrontier ℝ
      (convexHull ℝ (s.1.1 : Set E))) :
    (∀ i j : Σ s, γ s, i ≠ j → d i.1 i.2 ∩ d j.1 j.2 ⊆ r i.1 i.2 ∩ r j.1 j.2) ∧
    ∀ p ∈ ⋃ i : Σ s, γ s, r i.1 i.2, {i : Σ s, γ s | p ∈ r i.1 i.2}.ncard = 2 := by
  classical
  let F := {s : K.FaceOfCard 3 // s.1 ⊆ t}
  have hd (s : F) (i : γ s) : d s i ⊆ convexHull ℝ (s.1.1 : Set E) :=
    fun _ hx => hsub s (mem_iUnion.mpr ⟨i, hx⟩)
  have hsmall (s : F) {a : Finset E} (has : a ⊆ s.1.1) (ha : a.card = 2) :
      convexHull ℝ (a : Set E) ⊆ intrinsicFrontier ℝ
        (convexHull ℝ (s.1.1 : Set E)) := by
    apply (K.indep s.1.2.1).convexHull_subset_intrinsicFrontier
    exact Finset.ssubset_iff_subset_ne.mpr ⟨has, fun heq => by
      have hh := congrArg Finset.card heq
      rw [ha, s.1.2.2] at hh
      omega⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨s, i⟩ ⟨u, j⟩ hne x ⟨hxi, hxj⟩
    by_cases hsu : s = u
    · subst u
      have hij : i ≠ j := fun h => hne (by cases h; rfl)
      exact (disjoint_left.mp (hdis s hij) hxi hxj).elim
    · have hsune : s.1.1 ≠ u.1.1 := fun h => hsu (Subtype.ext (Subtype.ext h))
      have hc := tetrahedral_triangle_inter_card_two s.2 u.2 s.1.2.2 u.1.2.2 ht4 hsune
      have hx : x ∈ convexHull ℝ ((s.1.1 ∩ u.1.1 : Finset E) : Set E) := by
        rw [Finset.coe_inter, ← K.convexHull_inter_convexHull s.1.2.1 u.1.2.1]
        exact ⟨hd s i hxi, hd u j hxj⟩
      exact ⟨(hrim s i).symm ▸ ⟨hxi, hsmall s Finset.inter_subset_left hc hx⟩,
        (hrim u j).symm ▸ ⟨hxj, hsmall u Finset.inter_subset_right hc hx⟩⟩
  · intro p hp
    obtain ⟨z, hz⟩ := mem_iUnion.mp hp
    have hpz := (hrim z.1 z.2).subset hz
    have hpS : g p ∈ S := ((hphysical z.1).subset
      ⟨p, mem_iUnion.mpr ⟨z.2, hpz.1⟩, rfl⟩).1
    have hpv : p ∉ K.vertices := fun hv =>
      disjoint_left.mp havoid hpS (mem_image_of_mem g hv)
    obtain ⟨v, hv, hpedge⟩ := ((K.indep z.1.1.2.1).mem_intrinsicFrontier_convexHull_finset
      (K.nonempty_of_mem_faces z.1.1.2.1) p).mp hpz.2
    let a := z.1.1.1.erase v
    have ha2 : a.card = 2 := by dsimp [a]; rw [Finset.card_erase_of_mem hv, z.1.1.2.2]
    have has : a ⊆ z.1.1.1 := Finset.erase_subset _ _
    have ha : a ∈ K.faces := K.down_closed z.1.1.2.1 has
      (Finset.card_pos.mp (by omega))
    have hpa : p ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)) := by
      by_contra hn
      have hpf : p ∈ intrinsicFrontier ℝ (convexHull ℝ (a : Set E)) := by
        rw [← intrinsicClosure_sdiff_intrinsicInterior]
        exact ⟨subset_intrinsicClosure hpedge, hn⟩
      obtain ⟨w, hw, hpw⟩ := ((K.indep ha).mem_intrinsicFrontier_convexHull_finset
        (K.nonempty_of_mem_faces ha) p).mp hpf
      have hc : (a.erase w).card = 1 := by rw [Finset.card_erase_of_mem hw, ha2]
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hc
      have hpb : p = b := by simpa only [hb, Finset.coe_singleton,
        convexHull_singleton, mem_singleton_iff] using hpw
      apply hpv
      change {p} ∈ K.faces
      rw [hpb, ← hb]
      exact K.down_closed ha (Finset.erase_subset _ _) (by rw [hb]; exact Finset.singleton_nonempty b)
    obtain ⟨s, u, hsu, hsK, huK, has', hau, hst, hut, hs3, hu3, hfaces⟩ :=
      exists_two_physical_triangle_cofaces_at_edge_point K g hgi ha ht
        (has.trans z.1.2) ha2 ht4 hpa
    let s' : F := ⟨⟨s, hsK, hs3⟩, hst⟩
    let u' : F := ⟨⟨u, huK, hu3⟩, hut⟩
    have hcontact (b : F) (hpb : p ∈ convexHull ℝ (b.1.1 : Set E)) :
        ∃! i, p ∈ d b i := by
      obtain ⟨x, hx, hxp⟩ := (hphysical b).symm.subset ⟨hpS, p, hpb, rfl⟩
      have hxp' : x = p := hgi (K.convexHull_subset_space b.1.2.1 (hsub b hx))
        (K.convexHull_subset_space b.1.2.1 hpb) hxp
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hxp' ▸ hx)
      refine ⟨i, hi, fun j hj => ?_⟩
      by_contra hji
      exact disjoint_left.mp (hdis b hji) hj hi
    obtain ⟨i, hi, hiu⟩ := hcontact s' (convexHull_mono has' hpedge)
    obtain ⟨j, hj, hju⟩ := hcontact u' (convexHull_mono hau hpedge)
    have hri : p ∈ r s' i := (hrim s' i).symm ▸ ⟨hi, hsmall s' has' ha2 hpedge⟩
    have hrj : p ∈ r u' j := (hrim u' j).symm ▸ ⟨hj, hsmall u' hau ha2 hpedge⟩
    apply ncard_eq_two.mpr
    refine ⟨⟨s', i⟩, ⟨u', j⟩, ?_, ?_⟩
    · exact fun h => hsu (congrArg (fun q : Σ s, γ s => q.1.1.1) h)
    · ext q
      constructor
      · intro hq
        have hqd := ((hrim q.1 q.2).subset hq).1
        have hqface := (hfaces q.1.1.1 q.1.2 q.1.1.2.2).mp
          (mem_image_of_mem g (hd q.1 q.2 hqd))
        rcases hqface with hqs | hqu
        · have he : q.1 = s' := Subtype.ext (Subtype.ext hqs)
          obtain ⟨b, k⟩ := q
          dsimp only at he
          subst b
          have hk := hiu k hqd
          exact Or.inl (by cases hk; rfl)
        · have he : q.1 = u' := Subtype.ext (Subtype.ext hqu)
          obtain ⟨b, k⟩ := q
          dsimp only at he
          subst b
          have hk := hju k hqd
          exact Or.inr (by cases hk; rfl)
      · rintro (rfl | rfl)
        · exact hri
        · exact hrj

end PoincareConjecture.M76
