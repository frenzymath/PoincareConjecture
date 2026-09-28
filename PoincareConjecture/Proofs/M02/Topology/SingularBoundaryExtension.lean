import PoincareConjecture.Proofs.M02.Topology.SingularHomotopyClasses
import PoincareConjecture.Proofs.M02.Topology.HomotopyAddition
import PoincareConjecture.Proofs.M02.Topology.SingularKan

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped BigOperators

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem singularPointedSimplex_relStruct_of_class_eq
    (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a b : (TopCat.toSSet.obj X).PtSimplex (n + 1) x)
    (h : singularPointedSimplexClass X n x a =
      singularPointedSimplexClass X n x b) :
    Nonempty (SSet.PtSimplex.RelStruct a b (0 : Fin (n + 2))) := by
  have hh : GenLoop.Homotopic (singularPointedSimplexGenLoop X n x a)
      (singularPointedSimplexGenLoop X n x b) := Quotient.exact h
  change ContinuousMap.HomotopicRel _ _ (Cube.boundary (Fin (n + 1))) at hh
  rw [singularPointedSimplexGenLoop_val, singularPointedSimplexGenLoop_val] at hh
  obtain ⟨H⟩ := (stdSimplex_cube_coordinates_homotopicRel_iff (n + 1)
    (stdSimplexCubeMap (n + 1)) (stdSimplexCubeMap_spec (n + 1)).1
    (stdSimplexCubeMap_spec (n + 1)).2 _ _).mp hh
  have split_add (t v : Real) : t * v + (1 - t) * v = v := by
    rw [← add_mul, (add_comm t (1 - t)).trans (sub_add_cancel 1 t), one_mul]
  let qval (p : unitInterval × stdSimplex Real (Fin (n + 2))) : Fin (n + 3) → Real :=
    Fin.cons (α := fun _ : Fin (n + 3) => Real) ((p.1 : Real) * p.2 0)
      (Fin.cons (α := fun _ : Fin (n + 2) => Real)
        ((1 - (p.1 : Real)) * p.2 0) (fun j : Fin (n + 1) => p.2 j.succ))
  have hqval (p : unitInterval × stdSimplex Real (Fin (n + 2))) :
      qval p ∈ stdSimplex Real (Fin (n + 3)) := by
    constructor
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact mul_nonneg p.1.property.1 (p.2.property.1 0)
      · refine Fin.cases ?_ (fun l => ?_) k
        · exact mul_nonneg (sub_nonneg.mpr p.1.property.2) (p.2.property.1 0)
        · exact p.2.property.1 l.succ
    · rw [Fin.sum_univ_succ]
      change (p.1 : Real) * p.2 0 +
        (∑ j : Fin (n + 2), Fin.cons ((1 - (p.1 : Real)) * p.2 0)
          (fun k : Fin (n + 1) => p.2 k.succ) j) = 1
      rw [Fin.sum_univ_succ]
      change (p.1 : Real) * p.2 0 +
        ((1 - (p.1 : Real)) * p.2 0 + ∑ j : Fin (n + 1), p.2 j.succ) = 1
      rw [← add_assoc, split_add]
      exact (Fin.sum_univ_succ p.2.val).symm.trans p.2.property.2
  have hqcont : Continuous qval := by
    have ht : Continuous (fun p : unitInterval × stdSimplex Real (Fin (n + 2)) =>
        (p.1 : Real)) := continuous_subtype_val.comp continuous_fst
    have hz (j : Fin (n + 2)) :
        Continuous (fun p : unitInterval × stdSimplex Real (Fin (n + 2)) => p.2 j) :=
      ((continuous_apply j).comp continuous_subtype_val).comp continuous_snd
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact ht.mul (hz 0)
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact (continuous_const.sub ht).mul (hz 0)
      · exact hz l.succ
  let Q : C(unitInterval × stdSimplex Real (Fin (n + 2)),
      stdSimplex Real (Fin (n + 3))) :=
    ⟨fun p => ⟨qval p, hqval p⟩, hqcont.subtype_mk hqval⟩
  have hsurj : Function.Surjective Q := by
    intro y
    let zval : Fin (n + 2) → Real :=
      Fin.cons (α := fun _ : Fin (n + 2) => Real) (y 0 + y 1)
        (fun j : Fin (n + 1) => y j.succ.succ)
    have hzval : zval ∈ stdSimplex Real (Fin (n + 2)) := by
      constructor
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · exact add_nonneg (y.property.1 0) (y.property.1 1)
        · exact y.property.1 k.succ.succ
      · rw [Fin.sum_univ_succ]
        change y 0 + y 1 + ∑ j : Fin (n + 1), y j.succ.succ = 1
        have hs := y.property.2
        rw [Fin.sum_univ_succ] at hs
        rw [Fin.sum_univ_succ] at hs
        exact (add_assoc _ _ _).trans hs
    let z : stdSimplex Real (Fin (n + 2)) := ⟨zval, hzval⟩
    by_cases hd : y 0 + y 1 = 0
    · have hy0 : y 0 = 0 := le_antisymm
        ((le_add_of_nonneg_right (y.property.1 1)).trans_eq hd) (y.property.1 0)
      have hy1 : y 1 = 0 := le_antisymm
        ((le_add_of_nonneg_left (y.property.1 0)).trans_eq hd) (y.property.1 1)
      refine ⟨(0, z), ?_⟩
      apply Subtype.ext
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · change (0 : Real) * (y 0 + y 1) = y 0
        rw [zero_mul, hy0]
      · refine Fin.cases ?_ (fun l => ?_) k
        · change (1 - (0 : Real)) * (y 0 + y 1) = y 1
          rw [sub_zero, one_mul, hd, hy1]
        · rfl
    · have hdpos : 0 < y 0 + y 1 :=
        lt_of_le_of_ne (add_nonneg (y.property.1 0) (y.property.1 1)) (Ne.symm hd)
      let t : unitInterval := ⟨y 0 / (y 0 + y 1),
        div_nonneg (y.property.1 0) hdpos.le,
        (div_le_one hdpos).mpr (le_add_of_nonneg_right (y.property.1 1))⟩
      refine ⟨(t, z), ?_⟩
      apply Subtype.ext
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · change (y 0 / (y 0 + y 1)) * (y 0 + y 1) = y 0
        exact div_mul_cancel₀ _ hd
      · refine Fin.cases ?_ (fun l => ?_) k
        · change (1 - y 0 / (y 0 + y 1)) * (y 0 + y 1) = y 1
          rw [sub_mul, one_mul, div_mul_cancel₀ _ hd, add_sub_cancel_left]
        · rfl
  have hfac : Function.FactorsThrough H.toHomotopy.toContinuousMap Q := by
    rintro ⟨t, z⟩ ⟨s, w⟩ hzw
    have hz0 : z 0 = w 0 := by
      have hs := congrArg (fun y : stdSimplex Real (Fin (n + 3)) => y 0 + y 1) hzw
      change (t : Real) * z 0 + (1 - (t : Real)) * z 0 =
        (s : Real) * w 0 + (1 - (s : Real)) * w 0 at hs
      simpa only [split_add] using hs
    have hzw' : z = w := by
      apply Subtype.ext
      funext j
      refine Fin.cases hz0 (fun k => ?_) j
      exact congrArg (fun y : stdSimplex Real (Fin (n + 3)) => y k.succ.succ) hzw
    subst w
    by_cases hz : z 0 = 0
    · exact (H.eq_fst t ⟨0, hz⟩).trans (H.eq_fst s ⟨0, hz⟩).symm
    · have ht : t = s := by
        apply Subtype.ext
        apply mul_right_cancel₀ hz
        exact congrArg (fun y : stdSimplex Real (Fin (n + 3)) => y 0) hzw
      subst s
      rfl
  have hQ := _root_.Topology.IsQuotientMap.of_surjective_continuous hsurj Q.continuous
  let R := hQ.lift H.toHomotopy.toContinuousMap hfac
  have hR : R.comp Q = H.toHomotopy.toContinuousMap :=
    hQ.lift_comp H.toHomotopy.toContinuousMap hfac
  have heval (t : unitInterval) (z : stdSimplex Real (Fin (n + 2))) :
      R (Q (t, z)) = H (t, z) := DFunLike.congr_fun hR (t, z)
  have hQ0 (z : stdSimplex Real (Fin (n + 2))) :
      Q (0, z) = stdSimplex.map (0 : Fin (n + 3)).succAbove z := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change (0 : Real) * z 0 = stdSimplex.map (0 : Fin (n + 3)).succAbove z 0
      rw [zero_mul]
      exact (stdSimplex_face_zero (n + 1) 0 z).symm
    · have hf := stdSimplex_face_succAbove (n + 1) (0 : Fin (n + 3)) z k
      rw [Fin.zero_succAbove] at hf
      change Q (0, z) k.succ = stdSimplex.map (0 : Fin (n + 3)).succAbove z k.succ
      rw [hf]
      refine Fin.cases ?_ (fun _ => rfl) k
      change (1 - (0 : Real)) * z 0 = z 0
      rw [sub_zero, one_mul]
  have hQ1 (z : stdSimplex Real (Fin (n + 2))) :
      Q (1, z) = stdSimplex.map (1 : Fin (n + 3)).succAbove z := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · have hf := stdSimplex_face_succAbove (n + 1) (1 : Fin (n + 3)) z 0
      rw [Fin.one_succAbove_zero] at hf
      change (1 : Real) * z 0 = stdSimplex.map (1 : Fin (n + 3)).succAbove z 0
      rw [one_mul]
      exact hf.symm
    · refine Fin.cases ?_ (fun l => ?_) k
      · change (1 - (1 : Real)) * z 0 = stdSimplex.map (1 : Fin (n + 3)).succAbove z 1
        rw [sub_self, zero_mul]
        exact (stdSimplex_face_zero (n + 1) 1 z).symm
      · have hf := stdSimplex_face_succAbove (n + 1) (1 : Fin (n + 3)) z l.succ
        rw [Fin.one_succAbove_succ] at hf
        exact hf.symm
  let G : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ TopCat.toSSet.obj X :=
    SSet.yonedaEquiv.symm ((X.toSSetObjEquiv _).symm R)
  have hG : X.toSSetObjEquiv _ (SSet.yonedaEquiv G) = R := by
    simp only [G, Equiv.apply_symm_apply]
  have face_ext (j : Fin (n + 3))
      (d : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 1))) ⟶ TopCat.toSSet.obj X)
      (hd : forall z : stdSimplex Real (Fin (n + 2)),
        R (stdSimplex.map j.succAbove z) = X.toSSetObjEquiv _ (SSet.yonedaEquiv d) z) :
      SSet.stdSimplex.δ j ≫ G = d := by
    apply SSet.yonedaEquiv.injective
    apply (X.toSSetObjEquiv _).injective
    ext z
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply, hG]
    exact hd z
  refine ⟨{ map := G
            δ_castSucc_map := ?_
            δ_succ_map := ?_
            δ_map_of_lt := ?_
            δ_map_of_gt := ?_ }⟩
  · change SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ G = a.map
    apply face_ext
    intro z
    rw [← hQ0, heval]
    exact H.apply_zero z
  · change SSet.stdSimplex.δ (1 : Fin (n + 3)) ≫ G = b.map
    apply face_ext
    intro z
    rw [← hQ1, heval]
    exact H.apply_one z
  · intro j hj
    exact False.elim (Fin.not_lt_zero j hj)
  · intro j hj
    apply face_ext
    intro z
    rw [singular_const_apply]
    cases j using Fin.cases with
    | zero => simp at hj
    | succ j =>
      cases j using Fin.cases with
      | zero => simp at hj
      | succ k =>
        obtain ⟨⟨t, w⟩, hw⟩ := hsurj (stdSimplex.map k.succ.succ.succAbove z)
        have hw0 : w k.succ = 0 :=
          (congrArg (fun y : stdSimplex Real (Fin (n + 3)) => y k.succ.succ) hw).trans
            (stdSimplex_face_zero (n + 1) k.succ.succ z)
        rw [← hw, heval]
        exact (H.eq_fst t ⟨k.succ, hw0⟩).trans
          (singular_pointedSimplex_boundary X n x a w ⟨k.succ, hw0⟩)

theorem exists_kan_simplex_face_zero_replacement
    (Y : SSet.{u}) [SSet.KanComplex Y] (n : Nat)
    (x : Y.obj (Opposite.op (SimplexCategory.mk 0)))
    (F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ Y)
    (a : Fin (n + 3) -> Y.PtSimplex (n + 1) x)
    (hF : forall j, SSet.stdSimplex.δ j ≫ F = (a j).map)
    (b : Y.PtSimplex (n + 1) x)
    (r : SSet.PtSimplex.RelStruct (a 0) b (0 : Fin (n + 2))) :
    Exists fun G : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ Y =>
      SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ G = b.map ∧
        forall (j : Fin (n + 3)), j ≠ 0 ->
          SSet.stdSimplex.δ j ≫ G = (a j).map := by
  classical
  have rel_faces (f g : Y.PtSimplex (n + 1) x) (i : Fin (n + 2))
      (s : SSet.PtSimplex.RelStruct f g i) (k : Fin (n + 3)) :
      SSet.stdSimplex.δ k ≫ s.map =
        if k.val = i.val then f.map else
        if k.val = i.val + 1 then g.map else SSet.const x := by
    by_cases h0 : k.val = i.val
    · have hk : k = i.castSucc := Fin.ext h0
      subst k
      simpa only [Fin.val_castSucc, if_pos rfl, ite_true] using s.δ_castSucc_map
    by_cases h1 : k.val = i.val + 1
    · have hk : k = i.succ := Fin.ext h1
      subst k
      simpa only [Fin.val_succ, Nat.add_one_ne_self, if_false, if_pos rfl, ite_true] using
        s.δ_succ_map
    rw [if_neg h0, if_neg h1]
    by_cases hk : k < i.castSucc
    · exact s.δ_map_of_lt k hk
    · apply s.δ_map_of_gt k
      change i.val + 1 < k.val
      change ¬k.val < i.val at hk
      omega
  let idx (j : Fin (n + 4)) : Fin (n + 3) := ⟨j.val - 1, by omega⟩
  let q : Fin (n + 4) := ⟨2, by omega⟩
  let D (j : Fin (n + 4)) (_ : j ≠ q) :
      (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ Y :=
    if j.val = 0 then r.map else
    if j.val = 1 then F else
      (SSet.PtSimplex.RelStruct.refl (a (idx j)) (1 : Fin (n + 2))).map
  have D_faces (j : Fin (n + 4)) (hj : j ≠ q) (k : Fin (n + 3)) :
      SSet.stdSimplex.δ k ≫ D j hj =
        if j.val = 0 then
          (if k.val = 0 then (a 0).map else if k.val = 1 then b.map else SSet.const x) else
        if j.val = 1 then (a k).map else
          (if k.val = 1 then (a (idx j)).map else
           if k.val = 2 then (a (idx j)).map else SSet.const x) := by
    dsimp only [D]
    by_cases h0 : j.val = 0
    · simp only [if_pos h0]
      exact rel_faces (a 0) b 0 r k
    simp only [if_neg h0]
    by_cases h1 : j.val = 1
    · simp only [if_pos h1]
      exact hF k
    simp only [if_neg h1]
    exact rel_faces _ _ 1 (SSet.PtSimplex.RelStruct.refl (a (idx j)) 1) k
  have compat : SSet.horn.IsCompatible D := by
    intro j k hj hk hjk
    rw [D_faces j hj, D_faces k hk]
    change j.val < k.val at hjk
    have hjq : j.val ≠ 2 := fun h => hj (Fin.ext h)
    have hkq : k.val ≠ 2 := fun h => hk (Fin.ext h)
    have hk0 : k.val ≠ 0 := by omega
    change
      (if j.val = 0 then
        (if k.val - 1 = 0 then (a 0).map else
         if k.val - 1 = 1 then b.map else SSet.const x) else
       if j.val = 1 then (a ⟨k.val - 1, by omega⟩).map else
        (if k.val - 1 = 1 then (a (idx j)).map else
         if k.val - 1 = 2 then (a (idx j)).map else SSet.const x)) =
      (if k.val = 0 then
        (if j.val = 0 then (a 0).map else if j.val = 1 then b.map else SSet.const x) else
       if k.val = 1 then (a ⟨j.val, by omega⟩).map else
        (if j.val = 1 then (a (idx k)).map else
         if j.val = 2 then (a (idx k)).map else SSet.const x))
    by_cases hj0 : j.val = 0
    · by_cases hk1 : k.val = 1
      · rw [if_pos hj0, if_pos (by omega : k.val - 1 = 0), if_neg hk0, if_pos hk1]
        exact congrArg (fun l : Fin (n + 3) => (a l).map) (Fin.ext hj0.symm)
      · rw [if_pos hj0, if_neg (by omega : k.val - 1 ≠ 0),
          if_neg (by omega : k.val - 1 ≠ 1), if_neg hk0, if_neg hk1,
          if_neg (by omega : j.val ≠ 1), if_neg hjq]
    · by_cases hj1 : j.val = 1
      · rw [if_neg hj0, if_pos hj1, if_neg hk0,
          if_neg (by omega : k.val ≠ 1), if_pos hj1]
      · rw [if_neg hj0, if_neg hj1, if_neg (by omega : k.val - 1 ≠ 1),
          if_neg (by omega : k.val - 1 ≠ 2), if_neg hk0,
          if_neg (by omega : k.val ≠ 1), if_neg hj1, if_neg hjq]
  obtain ⟨W, hW⟩ := compat.exists_lift_of_kanComplex
  have G_faces (j : Fin (n + 3)) :
      SSet.stdSimplex.δ j ≫ SSet.stdSimplex.δ q ≫ W =
        if j.val = 0 then b.map else (a j).map := by
    by_cases hj0 : j = 0
    · subst j
      have h0 : (0 : Fin (n + 3)).castSucc < q := by
        change (0 : Nat) < 2
        exact Nat.zero_lt_succ 1
      rw [CosimplicialObject.δ_comp_δ'_assoc SSet.stdSimplex h0,
        hW _ (ne_of_lt h0)]
      change SSet.stdSimplex.δ (1 : Fin (n + 3)) ≫ r.map = b.map
      exact r.δ_succ_map
    have hj0v : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    by_cases hj1 : j = 1
    · subst j
      have h1 : (1 : Fin (n + 3)).castSucc < q := by
        change (1 : Nat) < 2
        exact Nat.lt_succ_self 1
      rw [CosimplicialObject.δ_comp_δ'_assoc SSet.stdSimplex h1,
        hW _ (ne_of_lt h1)]
      change SSet.stdSimplex.δ (1 : Fin (n + 3)) ≫ F = (a 1).map
      exact hF 1
    have hj1v : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
    have hqj : q ≤ j.castSucc := by change 2 ≤ j.val; omega
    have hqs : q < j.succ := by change 2 < j.val + 1; omega
    rw [← CosimplicialObject.δ_comp_δ''_assoc SSet.stdSimplex hqj,
      hW j.succ (ne_of_gt hqs)]
    dsimp only [D]
    rw [if_neg (show j.succ.val ≠ 0 by change j.val + 1 ≠ 0; omega),
      if_neg (show j.succ.val ≠ 1 by change j.val + 1 ≠ 1; omega), if_neg hj0v]
    have he := (SSet.PtSimplex.RelStruct.refl (a (idx j.succ)) (1 : Fin (n + 2))).δ_succ_map
    apply he.trans
    exact congrArg (fun l : Fin (n + 3) => (a l).map) (Fin.ext (Nat.add_sub_cancel j.val 1))
  refine ⟨SSet.stdSimplex.δ q ≫ W, ?_, ?_⟩
  · simpa only [Fin.val_zero, if_pos rfl, ite_true] using G_faces 0
  · intro j hj
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simpa only [if_neg hjv] using G_faces j

theorem singular_pointed_simplex_boundary_extension_iff
    (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a : Fin (n + 4) -> (TopCat.toSSet.obj X).PtSimplex (n + 2) x) :
    (Exists fun F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶
        TopCat.toSSet.obj X =>
      forall j, SSet.stdSimplex.δ j ≫ F = (a j).map) ↔
    (∑ j : Fin (n + 4), ((-1 : Int) ^ j.val) •
      Additive.ofMul (singularPointedSimplexClass X (n + 1) x (a j))) = 0 := by
  classical
  let Y := TopCat.toSSet.obj X
  have : SSet.KanComplex Y := singular_kanComplex X
  let v (f : Y.PtSimplex (n + 2) x) :=
    Additive.ofMul (singularPointedSimplexClass X (n + 1) x f)
  have hzero : v SSet.RelativeMorphism.const = 0 :=
    congrArg Additive.ofMul (singularPointedSimplexClass_const X (n + 1) x)
  have hrel (f g : Y.PtSimplex (n + 2) x) (i : Fin (n + 3))
      (r : SSet.PtSimplex.RelStruct f g i) : v f = v g :=
    congrArg Additive.ofMul (singularPointedSimplexClass_eq_of_relStruct X (n + 1) x f g i r)
  have hmul (f g c : Y.PtSimplex (n + 2) x)
      (r : SSet.PtSimplex.MulStruct f g c (0 : Fin (n + 2))) : v c = v f + v g :=
    congrArg Additive.ofMul (singularPointedSimplexClass_mul X n x f g c r)
  constructor
  · rintro ⟨F, hF⟩
    exact pointedSimplex_alternating_face_sum Y n x v hzero hrel hmul F a hF
  · intro ha
    obtain ⟨F, b, hb, hF⟩ := exists_kan_pointedSimplex_horn_filler Y (n + 1) x
      (0 : Fin (n + 4)) (fun j _ => a j)
    let c (j : Fin (n + 4)) : Y.PtSimplex (n + 2) x := if j = 0 then b else a j
    have hc (j : Fin (n + 4)) : SSet.stdSimplex.δ j ≫ F = (c j).map := by
      by_cases hj : j = 0
      · subst j
        simpa only [c, if_pos rfl] using hb
      · simpa only [c, if_neg hj] using hF j hj
    have hadd := pointedSimplex_alternating_face_sum Y n x v hzero hrel hmul F c hc
    have hb0 : v b = v (a 0) := by
      rw [Fin.sum_univ_succ] at hadd ha
      simp only [Fin.val_zero, pow_zero, one_zsmul, c, if_pos rfl,
        Fin.succ_ne_zero, if_false] at hadd
      simp only [Fin.val_zero, pow_zero, one_zsmul] at ha
      exact add_right_cancel (hadd.trans ha.symm)
    have hclass : singularPointedSimplexClass X (n + 1) x b =
        singularPointedSimplexClass X (n + 1) x (a 0) := congrArg Additive.toMul hb0
    obtain ⟨r⟩ := singularPointedSimplex_relStruct_of_class_eq X (n + 1) x b (a 0) hclass
    have r' : SSet.PtSimplex.RelStruct (c 0) (a 0) (0 : Fin (n + 3)) := by
      simpa only [c, if_pos rfl] using r
    obtain ⟨G, hG0, hG⟩ := exists_kan_simplex_face_zero_replacement Y (n + 1) x F c hc
      (a 0) r'
    refine ⟨G, fun j => ?_⟩
    by_cases hj : j = 0
    · subst j
      exact hG0
    · simpa only [c, if_neg hj] using hG j hj

end PoincareConjecture.Proofs.M02.Topology
