import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.TwoCapIncidence
import PoincareConjecture.Proofs.M76.Mathlib.PureTriangleClosedStar



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

private abbrev z (x : E) : E × ℝ := (x, 0)
private abbrev a (b : Bool) : E × ℝ := (0, capSign b)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E] in
private theorem zi : Function.Injective (z (E := E)) := fun _ _ h ↦ congrArg Prod.fst h

omit [NormedSpace ℝ E] [DecidableEq E] in
private theorem az (b : Bool) (x : E) : a b ≠ z x := by
  intro h
  have hs := congrArg Prod.snd h
  cases b <;> norm_num [a, z, capSign] at hs

variable (K : SimplicialComplex ℝ E) (L : Bool → SimplicialComplex ℝ E)
  (J : SimplicialComplex ℝ (E × ℝ))
  (hfaces : ∀ s, s ∈ J.faces ↔
    (∃ t ∈ K.faces, s = t.image z) ∨
    ∃ b : Bool, s = {a b} ∨ ∃ t ∈ (L b).faces, s = insert (a b) (t.image z))

include hfaces



theorem two_cap_link_isConnected_at_base
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hLK : ∀ b, L b ≤ K)
    (hLpure : ∀ b s, s ∈ (L b).faces → ∃ t ∈ (L b).faces, t.card = 2 ∧ s ⊆ t)
    (hne : ∀ b, (L b).space.Nonempty)
    (v : E) (hlink : IsConnected (K.link v).space) :
    IsConnected (J.link (z v)).space := by
  let Z : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hconv (s : Finset E) : z '' convexHull ℝ (s : Set E) =
      convexHull ℝ (s.image z : Set (E × ℝ)) := by
    have hZ : (Z.toAffineMap : E → E × ℝ) = z := by funext x; rfl
    simpa only [hZ, Finset.coe_image] using Z.toAffineMap.image_convexHull (s : Set E)
  have hJpure := two_cap_pure K L J hfaces hpure hLpure hne
  let I := {p : Bool × E // v ≠ p.2 ∧ ({v, p.2} : Finset E) ∈ (L p.1).faces}
  let F : Option I → Set (E × ℝ)
    | none => z '' (K.link v).space
    | some p => segment ℝ (a p.val.1) (z p.val.2)
  have hneighbor (p : I) : p.val.2 ∈ (K.link v).vertices := by
    have hedge := hLK p.val.1 p.property.2
    exact ⟨K.down_closed hedge (by simp) (by simp), by
      simpa only [Finset.mem_singleton] using p.property.1, hedge⟩
  have hbase : IsConnected (F none) := hlink.image z Z.continuous.continuousOn
  have hF (i : Option I) : IsConnected (F i) := by
    cases i with
    | none => exact hbase
    | some p =>
      exact (convex_segment (a p.val.1) (z p.val.2)).isConnected
        ⟨_, left_mem_segment ℝ _ _⟩
  have hmeet (i : Option I) : (F i ∩ F none).Nonempty := by
    cases i with
    | none => exact hbase.nonempty.mono (by simp)
    | some p => exact ⟨z p.val.2, right_mem_segment ℝ _ _,
        mem_image_of_mem _ ((K.link v).vertices_subset_space (hneighbor p))⟩
  have hconn : IsConnected (⋃ i, F i) := by
    apply IsConnected.iUnion_of_reflTransGen hF
    intro i j
    have hi : Relation.ReflTransGen (fun i j : Option I ↦ (F i ∩ F j).Nonempty) i none :=
      Relation.ReflTransGen.single (hmeet i)
    exact hi.trans (Relation.ReflTransGen.single (by
      simpa only [inter_comm] using hmeet j))
  have hbaseIn : F none ⊆ (J.link (z v)).space := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hsJ : s.image z ∈ (J.link (z v)).faces := by
      refine ⟨(hfaces _).mpr (Or.inl ⟨s, hs.1, rfl⟩), ?_, ?_⟩
      · rintro hv
        obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
        exact hs.2.1 (zi hwv ▸ hw)
      · apply (hfaces _).mpr
        exact Or.inl ⟨insert v s, hs.2.2, (Finset.image_insert _ _ _).symm⟩
    exact (J.link (z v)).convexHull_subset_space hsJ
      ((hconv s).subset (mem_image_of_mem z hxs))
  have hsegmentIn (p : I) : F (some p) ⊆ (J.link (z v)).space := by
    have hsJ : ({a p.val.1, z p.val.2} : Finset (E × ℝ)) ∈ (J.link (z v)).faces := by
      have hvL : {p.val.2} ∈ (L p.val.1).faces :=
        (L p.val.1).down_closed p.property.2 (by simp) (by simp)
      refine ⟨(hfaces _).mpr (Or.inr ⟨p.val.1, Or.inr ⟨{p.val.2}, hvL, by simp⟩⟩), ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (he | he)
        · exact az p.val.1 v he.symm
        · exact p.property.1 (zi he)
      · apply (hfaces _).mpr
        refine Or.inr ⟨p.val.1, Or.inr ⟨{v, p.val.2}, p.property.2, ?_⟩⟩
        simp only [Finset.image_insert, Finset.image_singleton, Finset.insert_comm]
    simpa only [Finset.coe_pair, convexHull_pair] using
      (J.link (z v)).convexHull_subset_space hsJ
  have hcover : (J.link (z v)).space = ⋃ i, F i := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hs, hsc, hvs, hxs⟩ :=
        (J.mem_link_space_iff_triangle hJpure (z v) x).mp hx
      rcases (two_cap_triangle_iff K L J hfaces s).mp ⟨hs, hsc⟩ with
        ⟨u, hu, huc, rfl⟩ | ⟨b, u, hu, huc, rfl⟩
      · have hvu : v ∈ u := by
          obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvs
          exact zi hwv ▸ hw
        have he : (u.image z : Set (E × ℝ)) \ {z v} =
            ((u.erase v).image z : Set (E × ℝ)) := by
          rw [Finset.image_erase zi, Finset.coe_erase]
        rw [he, ← hconv] at hxs
        obtain ⟨y, hy, rfl⟩ := hxs
        have hyK : y ∈ (K.link v).space := by
          apply (K.mem_link_space_iff_triangle hpure v y).mpr
          exact ⟨u, hu, huc, hvu, by simpa only [Finset.coe_erase] using hy⟩
        exact mem_iUnion.mpr ⟨none, mem_image_of_mem z hyK⟩
      · have hvu : v ∈ u := by
          rcases Finset.mem_insert.mp hvs with he | he
          · exact (az b v he.symm).elim
          · obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp he
            exact zi hwv ▸ hw
        obtain ⟨w, hw, huw⟩ : ∃ w, v ≠ w ∧ u = {v, w} := by
          obtain ⟨w₀, w₁, hww, he⟩ := Finset.card_eq_two.mp huc
          rw [he] at hvu
          rcases Finset.mem_insert.mp hvu with hv | hv
          · exact ⟨w₁, hv ▸ hww, hv ▸ he⟩
          · have hv := Finset.mem_singleton.mp hv
            exact ⟨w₀, hv ▸ hww.symm, by simpa only [hv, Finset.pair_comm] using he⟩
        subst u
        let p : I := ⟨(b, w), hw, hu⟩
        refine mem_iUnion.mpr ⟨some p, ?_⟩
        have he : ((insert (a b) (({v, w} : Finset E).image z) : Finset (E × ℝ)) : Set (E × ℝ)) \
            {z v} = {a b, z w} := by
          ext y
          simp only [Finset.image_insert, Finset.image_singleton, Finset.coe_insert,
            Finset.coe_singleton, mem_sdiff, mem_insert_iff, mem_singleton_iff]
          have hzvw : z v ≠ z w := fun h ↦ hw (zi h)
          constructor
          · rintro ⟨h | h | h, hy⟩
            · exact Or.inl h
            · exact (hy h).elim
            · exact Or.inr h
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, az b v⟩
            · exact ⟨Or.inr (Or.inr rfl), hzvw.symm⟩
        simpa only [he, convexHull_pair] using hxs
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      cases i with
      | none => exact hbaseIn hi
      | some p => exact hsegmentIn p hi
  exact hcover.symm ▸ hconn


theorem two_cap_apex_link_space (hLK : ∀ b, L b ≤ K) (b : Bool) :
    (J.link (a b)).space = z '' (L b).space := by
  have anot (c : Bool) (s : Finset E) : a c ∉ s.image z := by
    rintro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
    exact az c x hx.symm
  have ai : Function.Injective (a (E := E)) := by
    intro c d h
    have hs := congrArg Prod.snd h
    cases c <;> cases d
    · rfl
    · norm_num [a, capSign] at hs
    · norm_num [a, capSign] at hs
    · rfl
  let Z : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hconv (s : Finset E) : z '' convexHull ℝ (s : Set E) =
      convexHull ℝ (s.image z : Set (E × ℝ)) := by
    have hZ : (Z.toAffineMap : E → E × ℝ) = z := by funext x; rfl
    simpa only [hZ, Finset.coe_image] using Z.toAffineMap.image_convexHull (s : Set E)
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hcases := (hfaces (insert (a b) s)).mp hs.2.2
    rcases hcases with ⟨u, hu, he⟩ | ⟨c, he | ⟨u, hu, he⟩⟩
    · exact (anot b u (he ▸ Finset.mem_insert_self _ _)).elim
    · have hbc : b = c := ai (Finset.mem_singleton.mp (he ▸ Finset.mem_insert_self _ _))
      subst c
      obtain ⟨w, hw⟩ := J.nonempty_of_mem_faces hs.1
      have hw' : w = a b := Finset.mem_singleton.mp (he ▸ Finset.mem_insert_of_mem hw)
      exact (hs.2.1 (hw' ▸ hw)).elim
    · have hbc : b = c := by
        rcases Finset.mem_insert.mp (he ▸ Finset.mem_insert_self _ _) with h | h
        · exact ai h
        · exact (anot b u h).elim
      subst c
      have hsimage : s = u.image z := by
        have h := congrArg (fun t : Finset (E × ℝ) ↦ t.erase (a b)) he
        simpa only [Finset.erase_insert hs.2.1, Finset.erase_insert (anot b u)] using h
      rw [hsimage, ← hconv] at hxs
      obtain ⟨y, hy, rfl⟩ := hxs
      exact mem_image_of_mem z ((L b).convexHull_subset_space hu hy)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hsJ : s.image z ∈ (J.link (a b)).faces := by
      exact ⟨(hfaces _).mpr (Or.inl ⟨s, hLK b hs, rfl⟩), anot b s,
        (hfaces _).mpr (Or.inr ⟨b, Or.inr ⟨s, hs, rfl⟩⟩)⟩
    exact (J.link (a b)).convexHull_subset_space hsJ
      ((hconv s).subset (mem_image_of_mem z hxs))



theorem two_cap_links_isConnected
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hLK : ∀ b, L b ≤ K)
    (hLpure : ∀ b s, s ∈ (L b).faces → ∃ t ∈ (L b).faces, t.card = 2 ∧ s ⊆ t)
    (hLconn : ∀ b, IsConnected (L b).space)
    (hKlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space) :
    ∀ p ∈ J.vertices, IsConnected (J.link p).space := by
  intro p hp
  rcases (hfaces {p}).mp hp with ⟨u, hu, he⟩ | ⟨b, he | ⟨u, hu, he⟩⟩
  · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hu
    have hpv : p = z v := (Finset.mem_singleton.mp
      (he.symm ▸ Finset.mem_image_of_mem z hv)).symm
    rw [hpv]
    exact two_cap_link_isConnected_at_base K L J hfaces hpure hLK hLpure
      (fun b ↦ (hLconn b).nonempty) v
      (hKlinks v (K.down_closed hu (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)))
  · have hpv : p = a b := Finset.singleton_injective he
    rw [hpv, two_cap_apex_link_space K L J hfaces hLK]
    exact (hLconn b).image z (continuous_id.prodMk continuous_const).continuousOn
  · have hpa : p = a b := (Finset.mem_singleton.mp (he.symm ▸ Finset.mem_insert_self _ _)).symm
    obtain ⟨v, hv⟩ := (L b).nonempty_of_mem_faces hu
    have hpv : p = z v := (Finset.mem_singleton.mp
      (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_image_of_mem z hv))).symm
    exact (az b v (hpa.symm.trans hpv)).elim

end PoincareConjecture.M76.Dehn.Annuli
