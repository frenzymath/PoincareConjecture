import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphRealization
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false
open Set StdSimplexCore

namespace PoincareConjecture.M76.CutGraph

private theorem face_inter_eq {J : Type*} [Fintype J] [DecidableEq J]
    (s t : Finset J) :
    barycentricFace s ∩ barycentricFace t = barycentricFace (s ∩ t) := by
  ext x
  constructor
  · rintro ⟨⟨hx, hs⟩, _, ht⟩
    refine ⟨hx, fun j hj => ?_⟩
    by_cases hjs : j ∈ s
    · exact ht j (fun hjt => hj (Finset.mem_inter.mpr ⟨hjs, hjt⟩))
    · exact hs j hjs
  · rintro ⟨hx, h⟩
    exact ⟨⟨hx, fun j hj => h j (fun hh => hj (Finset.mem_inter.mp hh).1)⟩,
      hx, fun j hj => h j (fun hh => hj (Finset.mem_inter.mp hh).2)⟩

private theorem face_singleton_eq {J : Type*} [Fintype J] [DecidableEq J] (a : J) :
    barycentricFace {a} = {Pi.single a (1 : ℝ)} := by
  rw [barycentricFace_eq_convexHull]
  simp

private theorem single_mem_face_iff {J : Type*} [Fintype J] [DecidableEq J]
    (a : J) (s : Finset J) : Pi.single a (1 : ℝ) ∈ barycentricFace s ↔ a ∈ s := by
  constructor
  · intro h
    by_contra ha
    simpa using h.2 a ha
  · intro ha
    rw [barycentricFace_eq_convexHull]
    exact subset_convexHull ℝ _ (mem_image_of_mem _ ha)

def faceCoordinate {J : Type*} [Fintype J] [DecidableEq J]
    (s : Finset J) (j : J) (x : barycentricFace s) : unitInterval :=
  ⟨x.val j, x.property.1.1 j, by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => x.property.1.1 k)
      (Finset.mem_univ j)
    exact h.trans_eq x.property.1.2⟩

private theorem continuous_faceCoordinate {J : Type*} [Fintype J] [DecidableEq J]
    (s : Finset J) (j : J) : Continuous (faceCoordinate s j) :=
  ((continuous_apply j).comp continuous_subtype_val).subtype_mk _

def coordinateGraphCarrier {J L : Type*} [Fintype J] [DecidableEq J]
    (a b : L → J) : Set (J → ℝ) :=
  Set.range (fun j : J => Pi.single j (1 : ℝ)) ∪ ⋃ l, barycentricFace {a l, b l}

theorem exists_coordinate_edge_map
    {J L Y : Type*} [Fintype J] [Fintype L] [DecidableEq J]
    [TopologicalSpace Y]
    (a b : L → J) (hne : ∀ l, a l ≠ b l)
    (hpairs : Function.Injective (fun l => ({a l, b l} : Finset J)))
    (f : J → Y) (p : ∀ l, Path (f (a l)) (f (b l))) :
    ∃ F : C(coordinateGraphCarrier a b, Y),
      (∀ j (x : coordinateGraphCarrier a b),
        (x : J → ℝ) = Pi.single j 1 → F x = f j) ∧
      (∀ l (x : coordinateGraphCarrier a b) (hx : (x : J → ℝ) ∈ barycentricFace {a l, b l}),
        F x = p l (faceCoordinate {a l, b l} (b l) ⟨x, hx⟩)) := by
  classical
  let R := Set.range (fun j : J => Pi.single j (1 : ℝ)) ∪
    ⋃ l, barycentricFace {a l, b l}
  let pieces : J ⊕ L → Set R := fun j => match j with
    | .inl j => {x | (x : J → ℝ) = Pi.single j 1}
    | .inr l => {x | (x : J → ℝ) ∈ barycentricFace {a l, b l}}
  let H : ∀ j, C(pieces j, Y) := fun j => match j with
    | .inl j => ContinuousMap.const _ (f j)
    | .inr l => ⟨fun x => p l (faceCoordinate _ (b l) ⟨x.val, x.property⟩),
        (p l).continuous.comp ((continuous_faceCoordinate _ _).comp
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))⟩
  have hend (l : L) (j : J) (x : pieces (.inr l))
      (hx : (x.val : J → ℝ) = Pi.single j 1) : H (.inr l) x = f j := by
    have hj := (single_mem_face_iff j {a l, b l}).mp (hx ▸ x.property)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    change p l (faceCoordinate _ (b l) ⟨x.val, x.property⟩) = f j
    rcases hj with rfl | rfl
    · have ht : faceCoordinate {a l, b l} (b l) ⟨x.val, x.property⟩ = 0 := by
        apply Subtype.ext
        simp [faceCoordinate, hx, Pi.single_eq_of_ne (hne l).symm]
      rw [ht, (p l).source]
    · have ht : faceCoordinate {a l, b l} (b l) ⟨x.val, x.property⟩ = 1 := by
        apply Subtype.ext
        simp [faceCoordinate, hx]
      rw [ht, (p l).target]
  have hH : ∀ j k (x : R) (hj : x ∈ pieces j) (hk : x ∈ pieces k),
      H j ⟨x, hj⟩ = H k ⟨x, hk⟩ := by
    intro j k x hj hk
    cases j with
    | inl j =>
      cases k with
      | inl k =>
        have he : j = k := by
          have hi := (Pi.linearIndependent_single_one J ℝ).injective
          exact hi (hj.symm.trans hk)
        subst k; rfl
      | inr l => exact (hend l j ⟨x, hk⟩ hj).symm
    | inr l =>
      cases k with
      | inl j => exact hend l j ⟨x, hj⟩ hk
      | inr m =>
        by_cases hlm : l = m
        · subst m; rfl
        have hneq := hpairs.ne hlm
        let s : Finset J := {a l, b l} ∩ {a m, b m}
        have hcard : s.card < 2 := by
          have hs : s ⊂ {a l, b l} := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
            intro he
            have hsub : ({a l, b l} : Finset J) ⊆ {a m, b m} :=
              he ▸ (show s ⊆ {a m, b m} from Finset.inter_subset_right)
            exact hneq (Finset.eq_of_subset_of_card_le hsub (by simp [hne]))
          simpa [hne l] using Finset.card_lt_card hs
        have hx : (x : J → ℝ) ∈ barycentricFace s :=
          (face_inter_eq {a l, b l} {a m, b m}).subset ⟨hj, hk⟩
        have hsne : s.Nonempty := by
          by_contra hs
          have he := Finset.not_nonempty_iff_eq_empty.mp hs
          rw [he, barycentricFace_eq_convexHull] at hx
          simp at hx
        have hc : s.card = 1 := by
          have := Finset.card_pos.mpr hsne
          omega
        obtain ⟨j, hsj⟩ := Finset.card_eq_one.mp hc
        have he : (x : J → ℝ) = Pi.single j 1 := by
          simpa only [hsj, face_singleton_eq, mem_singleton_iff] using hx
        exact (hend l j ⟨x, hj⟩ he).trans (hend m j ⟨x, hk⟩ he).symm
  have hcover : ⋃ j, pieces j = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    rcases x.property with ⟨j, hj⟩ | hx
    · exact ⟨.inl j, hj.symm⟩
    · obtain ⟨l, hl⟩ := mem_iUnion.mp hx
      exact ⟨.inr l, hl⟩
  let F := Set.liftCover pieces (fun j => H j) hH hcover
  have hval (j : J ⊕ L) (x : pieces j) : F x = H j x := Set.liftCover_coe x
  have hF : Continuous F := by
    apply (locallyFinite_of_finite pieces).continuous hcover
    · intro j
      cases j with
      | inl j => exact isClosed_eq continuous_subtype_val continuous_const
      | inr l => exact (isClosed_barycentricFace _).preimage continuous_subtype_val
    · intro j
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (pieces j).domRestrict F = H j := funext (hval j)
      rw [he]
      exact (H j).continuous
  exact ⟨⟨F, hF⟩, fun j x hx => hval (.inl j) ⟨x, hx⟩,
    fun l x hx => hval (.inr l) ⟨x, hx⟩⟩

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def subdivisionStart (ends : I → Bool → V) : I × Option Bool → Coordinate V I
  | (i, none) => Sum.inr (i, false)
  | (i, some b) => Sum.inl (ends i b)

def subdivisionEnd : I × Option Bool → Coordinate V I
  | (i, none) => Sum.inr (i, true)
  | (i, some b) => Sum.inr (i, b)

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
theorem subdivision_ends_ne (ends : I → Bool → V) (l : I × Option Bool) :
    subdivisionStart ends l ≠ subdivisionEnd l := by
  rcases l with ⟨i, _ | b⟩ <;> simp [subdivisionStart, subdivisionEnd]

omit [Fintype V] [Fintype I] in
theorem subdivision_pairs_injective (ends : I → Bool → V) :
    Function.Injective (fun l =>
      ({subdivisionStart ends l, subdivisionEnd l} : Finset (Coordinate V I))) := by
  rintro ⟨i, _ | a⟩ ⟨j, _ | b⟩ h
  all_goals
    have hs := congrArg (fun s : Finset (Coordinate V I) => (s : Set (Coordinate V I))) h
    simp only [Finset.coe_pair, Set.pair_eq_pair_iff, subdivisionStart, subdivisionEnd,
      Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Bool.false_eq_true,
      Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, false_and, and_true,
      or_false] at hs <;> simp_all

theorem coordinateGraphCarrier_subdivision (ends : I → Bool → V) :
    coordinateGraphCarrier (subdivisionStart ends) (subdivisionEnd (V := V)) =
      carrier ends := by
  ext x
  constructor
  · rintro (⟨j, rfl⟩ | hx)
    · cases j with
      | inl v => exact vertex_mem_carrier ends v
      | inr ib => exact edge_subset_carrier ends ib.1 (privateVertex_mem_edge ends ib.1 ib.2)
    · obtain ⟨⟨i, _ | b⟩, hx⟩ := mem_iUnion.mp hx
      · exact edge_subset_carrier ends i (Or.inl (Or.inr hx))
      · cases b
        · exact edge_subset_carrier ends i (Or.inl (Or.inl hx))
        · exact edge_subset_carrier ends i (Or.inr hx)
  · rintro (⟨v, rfl⟩ | hx)
    · exact Or.inl ⟨Sum.inl v, rfl⟩
    · obtain ⟨i, (hi | hi) | hi⟩ := mem_iUnion.mp hx
      · exact Or.inr (mem_iUnion.mpr ⟨(i, some false), hi⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨(i, none), hi⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨(i, some true), hi⟩)

theorem exists_subdivided_path_map {Y : Type*} [TopologicalSpace Y]
    (ends : I → Bool → V) (a : V → Y) (u : I → Bool → Y)
    (arms : ∀ i b, Path (a (ends i b)) (u i b))
    (cores : ∀ i, Path (u i false) (u i true)) :
    ∃ F : C(carrier ends, Y),
      (∀ v (x : carrier ends), (x : Ambient V I) = vertex v → F x = a v) ∧
      (∀ i b (x : carrier ends) (hx : (x : Ambient V I) ∈ arm ends i b),
        F x = arms i b (faceCoordinate (J := Coordinate V I)
          {Sum.inl (ends i b), Sum.inr (i, b)}
          (Sum.inr (i, b)) ⟨(x : Ambient V I), hx⟩)) ∧
      (∀ i (x : carrier ends) (hx : (x : Ambient V I) ∈ bridge i),
        F x = cores i (faceCoordinate (J := Coordinate V I) {Sum.inr (i, false), Sum.inr (i, true)}
          (Sum.inr (i, true)) ⟨(x : Ambient V I), hx⟩)) := by
  let f : Coordinate V I → Y
    | .inl v => a v
    | .inr (i, b) => u i b
  let paths : ∀ l, Path (f (subdivisionStart ends l)) (f (subdivisionEnd l))
    | (i, none) => cores i
    | (i, some b) => arms i b
  obtain ⟨G, hGv, hGe⟩ := exists_coordinate_edge_map (subdivisionStart ends)
    subdivisionEnd (subdivision_ends_ne ends) (subdivision_pairs_injective ends) f paths
  let e := Homeomorph.setCongr (coordinateGraphCarrier_subdivision ends).symm
  refine ⟨G.comp ⟨e, e.continuous⟩, ?_, ?_, ?_⟩
  · intro v x hx
    exact hGv (.inl v) (e x) hx
  · intro i b x hx
    exact hGe (i, some b) (e x) hx
  · intro i x hx
    exact hGe (i, none) (e x) hx

end PoincareConjecture.M76.CutGraph
