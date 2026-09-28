import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CyclicBoundaryPath
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PolygonalArc











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ}
  {p : Polygon E n} {q : Polygon E (m + 2)}

private theorem crosscut_vertex_count (hp : IsSimplePolygon p) (a b : Fin n)
    (hab : b ≠ a) (hfirst : q 0 = p a) (hlast : q (Fin.last (m + 1)) = p b)
    (havoid : Disjoint (polygonArcBoundary q \ {p a, p b}) (p.boundary ℝ)) :
    3 ≤ cyclicDistance a b + (m + 1) := by
  have hpos : 0 < cyclicDistance a b := by
    by_contra h
    have hz : cyclicDistance a b = 0 := by omega
    have hh := iterate_cyclicDistance a b
    rw [hz] at hh
    exact hab hh.symm
  by_contra h
  have hd : cyclicDistance a b = 1 := by omega
  have hm : m = 0 := by omega
  subst m
  have hrot : finRotate n a = b := by
    simpa only [hd, Function.iterate_one] using iterate_cyclicDistance a b
  have hedge : q.edgeSet ℝ (0 : Fin 2) = p.edgeSet ℝ a := by
    change q.edgeSet ℝ (0 : Fin 1).castSucc = p.edgeSet ℝ a
    rw [polygon_arcEdge_eq_segment q (0 : Fin 1), polygon_edgeSet_eq_segment, hrot]
    change segment ℝ (q 0) (q (Fin.last 1)) = segment ℝ (p a) (p b)
    rw [hfirst, hlast]
  let x := p.edgePath ℝ a (1 / 2 : ℝ)
  have hx : x ∈ p.edgeSet ℝ a := ⟨1 / 2, by constructor <;> norm_num, rfl⟩
  have hxa : x ≠ p a := by
    intro hh
    have he : (1 / 2 : ℝ) = 0 := hp.edgePath_injective a (by
      simpa only [x, Polygon.edgePath, AffineMap.lineMap_apply_zero] using hh)
    norm_num at he
  have hxb : x ≠ p b := by
    intro hh
    have he : (1 / 2 : ℝ) = 1 := hp.edgePath_injective a (by
      simpa only [x, Polygon.edgePath, AffineMap.lineMap_apply_one, hrot] using hh)
    norm_num at he
  exact Set.disjoint_left.mp havoid
    ⟨polygon_arcEdge_subset_boundary q (0 : Fin 1) (hedge.symm ▸ hx),
      fun he => he.elim hxa hxb⟩ (polygon_edgeSet_subset_boundary p a hx)



theorem IsSimplePolygon.exists_polygon_of_boundary_path_and_crosscut
    (hp : IsSimplePolygon p) (hq : IsSimplePolygonalArc q) (a b : Fin n) (hab : b ≠ a)
    (hfirst : q 0 = p a) (hlast : q (Fin.last (m + 1)) = p b)
    (havoid : Disjoint (polygonArcBoundary q \ {p a, p b}) (p.boundary ℝ)) :
    ∃ r : Polygon E (cyclicDistance a b + (m + 1)), IsSimplePolygon r ∧
      r.boundary ℝ = polygonCyclicPathBoundary p a b ∪ polygonArcBoundary q := by
  classical
  let d := cyclicDistance a b
  let N := d + (m + 1)
  have hd : d < n := cyclicDistance_lt a b
  have hN : 3 ≤ N := crosscut_vertex_count hp a b hab hfirst hlast havoid
  let r : Polygon E N := ⟨fun i => if hi : i.val ≤ d then
    p (cyclicArcIndex a d ⟨i.val, by omega⟩)
    else q ⟨N - i.val, by dsimp [N]; omega⟩⟩
  have hf (i : Fin N) (hi : i.val ≤ d) :
      r i = p (cyclicArcIndex a d ⟨i.val, by omega⟩) := by
    change (if hi : i.val ≤ d then _ else _) = _
    rw [dif_pos hi]
  have hb (i : Fin N) (hi : d ≤ i.val) :
      r i = q ⟨N - i.val, by dsimp [N]; omega⟩ := by
    by_cases he : i.val = d
    · rw [hf i (by omega)]
      have hi' : (⟨i.val, by omega⟩ : Fin (d + 1)) = Fin.last d := Fin.ext he
      rw [hi', cyclicArcIndex_last]
      change p ((finRotate n)^[cyclicDistance a b] a) = _
      rw [iterate_cyclicDistance, ← hlast]
      congr 1
      apply Fin.ext
      dsimp [N]
      omega
    · change (if hi : i.val ≤ d then _ else _) = _
      rw [dif_neg (by omega)]
  have hzero : r ⟨0, by omega⟩ = q 0 := by
    rw [hf _ (by simp)]
    exact hfirst.symm
  have hfront (i : Fin N) (hi : i.val < d) :
      r i = p (cyclicArcIndex a d (⟨i.val, hi⟩ : Fin d).castSucc) ∧
      r (finRotate N i) = p (cyclicArcIndex a d (⟨i.val, hi⟩ : Fin d).succ) := by
    constructor
    · exact hf i hi.le
    · have hiN : i.val < d + m := by omega
      have hrot : finRotate N i = ⟨i.val + 1, by dsimp [N]; omega⟩ :=
        finRotate_of_lt hiN
      rw [hrot, hf _ (by dsimp; omega)]
      rfl
  have hback (i : Fin N) (hi : d ≤ i.val) :
      r i = q (⟨N - i.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)).succ ∧
      r (finRotate N i) =
        q (⟨N - i.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)).castSucc := by
    constructor
    · rw [hb i hi]
      congr 1
      apply Fin.ext
      dsimp
      omega
    · by_cases hiN : i.val < d + m
      · have hrot : finRotate N i = ⟨i.val + 1, by dsimp [N]; omega⟩ :=
          finRotate_of_lt hiN
        rw [hrot, hb _ (by dsimp; omega)]
        congr 1
      · have he : i = Fin.last (d + m) := by apply Fin.ext; dsimp [N] at *; omega
        have hz : finRotate N i = ⟨0, by omega⟩ :=
          (congrArg (finRotate N) he).trans finRotate_last
        rw [hz, hzero]
        congr 1
        apply Fin.ext
        dsimp [N] at *
        omega
  have hedgeF (i : Fin N) (hi : i.val < d) :
      r.edgeSet ℝ i = p.edgeSet ℝ (cyclicArcIndex a d (⟨i.val, hi⟩ : Fin d).castSucc) := by
    rw [polygon_edgeSet_eq_segment, polygon_edgeSet_eq_segment,
      (hfront i hi).1, (hfront i hi).2, cyclicArcIndex_succ]
  have hedgeB (i : Fin N) (hi : d ≤ i.val) :
      r.edgeSet ℝ i =
        q.edgeSet ℝ (⟨N - i.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)).castSucc := by
    rw [polygon_edgeSet_eq_segment, polygon_arcEdge_eq_segment,
      (hback i hi).1, (hback i hi).2, segment_symm]
  have hvertexMixed (i j : Fin N) (hi : i.val ≤ d) (hj : d < j.val) : r i ≠ r j := by
    rw [hf i hi, hb j hj.le]
    intro he
    let k : Fin (m + 2) := ⟨N - j.val, by dsimp [N]; omega⟩
    have hk0 : k ≠ 0 := by
      intro hh
      have hh' := congrArg Fin.val hh
      dsimp [k] at hh'
      omega
    have hke : k ≠ Fin.last (m + 1) := by
      intro hh
      have hh' := congrArg Fin.val hh
      dsimp [k, N] at hh'
      omega
    have hkends : q k ∉ ({p a, p b} : Set E) := by
      rintro (hh | hh)
      · exact hk0 (hq.vertices_injective (hh.trans hfirst.symm))
      · exact hke (hq.vertices_injective (hh.trans hlast.symm))
    exact Set.disjoint_left.mp havoid ⟨polygon_vertex_mem_arcBoundary q k, hkends⟩
      (he ▸ polygon_vertex_mem_boundary p _)
  have hinj : Function.Injective r := by
    intro i j hij
    by_cases hi : i.val ≤ d
    · by_cases hj : j.val ≤ d
      · rw [hf i hi, hf j hj] at hij
        have hh := congrArg Fin.val (cyclicArcIndex_injective a hd (hp.vertices_injective hij))
        exact Fin.ext hh
      · exact (hvertexMixed i j hi (by omega) hij).elim
    · by_cases hj : j.val ≤ d
      · exact (hvertexMixed j i hj (by omega) hij.symm).elim
      · rw [hb i (by omega), hb j (by omega)] at hij
        have hh := congrArg Fin.val (hq.vertices_injective hij)
        apply Fin.ext
        dsimp at hh
        omega
  have hpairF (i : Fin N) (hi : i.val < d) :
      ({r i, r (finRotate N i)} : Set E) =
        {p (cyclicArcIndex a d (⟨i.val, hi⟩ : Fin d).castSucc),
          p (finRotate n (cyclicArcIndex a d (⟨i.val, hi⟩ : Fin d).castSucc))} := by
    rw [(hfront i hi).1, (hfront i hi).2, cyclicArcIndex_succ]
  have hpairB (i : Fin N) (hi : d ≤ i.val) :
      ({r i, r (finRotate N i)} : Set E) =
        {q (⟨N - i.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)).castSucc,
          q (⟨N - i.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)).succ} := by
    rw [(hback i hi).1, (hback i hi).2, pair_comm]
  have hmixed (i j : Fin N) (hi : i.val < d) (hj : d ≤ j.val) :
      r.edgeSet ℝ i ∩ r.edgeSet ℝ j ⊆
        {r i, r (finRotate N i)} ∩ {r j, r (finRotate N j)} := by
    rw [hedgeF i hi, hedgeB j hj, hpairF i hi, hpairB j hj]
    intro x hx
    have hxends : x ∈ ({p a, p b} : Set E) := by
      by_contra hh
      exact Set.disjoint_left.mp havoid
        ⟨polygon_arcEdge_subset_boundary q _ hx.2, hh⟩
        (polygon_edgeSet_subset_boundary p _ hx.1)
    have hends (k : Fin n) (l : Fin (m + 2)) (hkl : q l = p k) (hxk : x = p k) :
        x ∈ ({p (cyclicArcIndex a d (⟨i.val, hi⟩ : Fin d).castSucc),
          p (finRotate n (cyclicArcIndex a d (⟨i.val, hi⟩ : Fin d).castSucc))} : Set E) ∩
        {q (⟨N - j.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)).castSucc,
          q (⟨N - j.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)).succ} := by
      constructor
      · have hh := (hp.vertex_mem_edgeSet_iff k _).mp (hxk ▸ hx.1)
        rcases hh with hh | hh
        · exact Or.inl (hxk.trans (congrArg p hh))
        · exact Or.inr (hxk.trans (congrArg p hh))
      · have hxl : x = q l := hxk.trans hkl.symm
        have hh := (hq.vertex_mem_edgeSet_iff l _).mp (hxl ▸ hx.2)
        rcases hh with hh | hh
        · exact Or.inl (hxl.trans (congrArg q hh))
        · exact Or.inr (hxl.trans (congrArg q hh))
    rcases hxends with hx | hx
    · exact hends a 0 hfirst hx
    · exact hends b (Fin.last (m + 1)) hlast hx
  have hsimple : IsSimplePolygon r := by
    refine ⟨hN, hinj, ?_⟩
    intro i j hij
    by_cases hi : i.val < d
    · by_cases hj : j.val < d
      · rw [hedgeF i hi, hedgeF j hj, hpairF i hi, hpairF j hj]
        apply hp.edges_inter
        intro hh
        have hh' := congrArg Fin.val (cyclicArcIndex_injective a hd hh)
        exact hij (Fin.ext hh')
      · exact hmixed i j hi (by omega)
    · by_cases hj : j.val < d
      · intro x hx
        exact (hmixed j i hj (by omega) ⟨hx.2, hx.1⟩).symm
      · rw [hedgeB i (by omega), hedgeB j (by omega),
          hpairB i (by omega), hpairB j (by omega)]
        apply hq.edges_inter
        intro hh
        have hh' := congrArg Fin.val hh
        apply hij
        apply Fin.ext
        dsimp at hh'
        omega
  refine ⟨r, hsimple, subset_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff r x).mp hx
    by_cases hdi : i.val < d
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i.val, hdi⟩, hedgeF i hdi ▸ hi⟩)
    · exact Or.inr (polygon_arcEdge_subset_boundary q _ (hedgeB i (by omega) ▸ hi))
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      let i : Fin N := ⟨j.val, by dsimp [N, d]; have := j.isLt; omega⟩
      apply polygon_edgeSet_subset_boundary r i
      rw [hedgeF i j.isLt]
      exact hj
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      let i : Fin N := ⟨N - j.val - 1, by have := j.isLt; dsimp [N]; omega⟩
      have hi : d ≤ i.val := by dsimp [i, N]; have := j.isLt; omega
      apply polygon_edgeSet_subset_boundary r i
      rw [hedgeB i hi]
      have he : (⟨N - i.val - 1, by dsimp [N]; omega⟩ : Fin (m + 1)) = j := by
        apply Fin.ext
        dsimp [i, N]
        have := j.isLt
        omega
      rw [he]
      exact hj

end PoincareConjecture.M25.Topology3D
