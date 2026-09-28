import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.SingularComplex.KanMultiplication
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped BigOperators

universe u v

namespace Poincare.Topology

set_option maxHeartbeats 3000000 in

theorem pointedSimplex_alternating_face_sum
    (X : SSet.{u}) [SSet.KanComplex X] (n : Nat)
    (x : X.obj (Opposite.op (SimplexCategory.mk 0)))
    {A : Type v} [AddCommGroup A]
    (v : X.PtSimplex (n + 2) x -> A)
    (hzero : v SSet.RelativeMorphism.const = 0)
    (hrel : forall (a b : X.PtSimplex (n + 2) x) (i : Fin (n + 3)),
      SSet.PtSimplex.RelStruct a b i -> v a = v b)
    (hmul : forall (f g c : X.PtSimplex (n + 2) x),
      SSet.PtSimplex.MulStruct f g c (0 : Fin (n + 2)) ->
        v c = v f + v g)
    (F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X)
    (a : Fin (n + 4) -> X.PtSimplex (n + 2) x)
    (hfaces : forall j : Fin (n + 4), SSet.stdSimplex.δ j ≫ F = (a j).map) :
    (∑ j : Fin (n + 4), ((-1 : Int) ^ j.val) • v (a j)) = 0 := by
  classical
  let e : X.PtSimplex (n + 2) x := SSet.RelativeMorphism.const
  let S (a : Fin (n + 4) -> X.PtSimplex (n + 2) x) : A :=
    ∑ j : Fin (n + 4), ((-1 : Int) ^ j.val) • v (a j)
  have he : v e = 0 := hzero
  have add_mul (f g c : X.PtSimplex (n + 2) x) (i : Fin (n + 2))
      (r : SSet.PtSimplex.MulStruct f g c i) : v c = v f + v g :=
    pointedSimplex_additive_mulStruct X n x v hzero hmul f g c i r
  have mul_faces (f g c : X.PtSimplex (n + 2) x) (i : Fin (n + 2))
      (r : SSet.PtSimplex.MulStruct f g c i) (j : Fin (n + 4)) :
      SSet.stdSimplex.δ j ≫ r.map =
        if j.val = i.val then g.map else
        if j.val = i.val + 1 then c.map else
        if j.val = i.val + 2 then f.map else SSet.const x := by
    by_cases h0 : j.val = i.val
    · have hj : j = i.castSucc.castSucc := Fin.ext h0
      subst j
      simp
    by_cases h1 : j.val = i.val + 1
    · have hj : j = i.castSucc.succ := Fin.ext h1
      subst j
      simp
    by_cases h2 : j.val = i.val + 2
    · have hj : j = i.succ.succ := Fin.ext h2
      subst j
      simp [Nat.add_assoc]
    rw [if_neg h0, if_neg h1, if_neg h2]
    by_cases hj : j < i.castSucc.castSucc
    · exact r.δ_map_of_lt j hj
    · apply r.δ_map_of_gt j
      change i.val + 1 + 1 < j.val
      change ¬j.val < i.val at hj
      omega
  have rel_faces (f : X.PtSimplex (n + 2) x) (i : Fin (n + 3))
      (j : Fin (n + 4)) :
      SSet.stdSimplex.δ j ≫ (SSet.PtSimplex.RelStruct.refl f i).map =
        if j.val = i.val then f.map else
        if j.val = i.val + 1 then f.map else SSet.const x := by
    by_cases h0 : j.val = i.val
    · have hj : j = i.castSucc := Fin.ext h0
      subst j
      simpa only [Fin.val_castSucc, if_pos rfl, ite_true] using
        (SSet.PtSimplex.RelStruct.refl f i).δ_castSucc_map
    by_cases h1 : j.val = i.val + 1
    · have hj : j = i.succ := Fin.ext h1
      subst j
      simpa only [Fin.val_succ, Nat.add_one_ne_self, if_false, if_pos rfl, ite_true] using
        (SSet.PtSimplex.RelStruct.refl f i).δ_succ_map
    rw [if_neg h0, if_neg h1]
    by_cases hj : j < i.castSucc
    · exact (SSet.PtSimplex.RelStruct.refl f i).δ_map_of_lt j hj
    · apply (SSet.PtSimplex.RelStruct.refl f i).δ_map_of_gt j
      change i.val + 1 < j.val
      change ¬j.val < i.val at hj
      omega
  have left_factor (f c : X.PtSimplex (n + 2) x) (i : Fin (n + 2)) :
      Exists fun g : X.PtSimplex (n + 2) x =>
        Nonempty (SSet.PtSimplex.MulStruct f g c i) := by
    let L : Fin (n + 4) := i.castSucc.castSucc
    let C : Fin (n + 4) := i.castSucc.succ
    let U : Fin (n + 4) := i.succ.succ
    let family (j : Fin (n + 4)) (_ : j ≠ L) : X.PtSimplex (n + 2) x :=
      if j = C then c else if j = U then f else e
    obtain ⟨B, g, hg, hB⟩ :=
      exists_kan_pointedSimplex_horn_filler X (n + 1) x L family
    refine ⟨g, ⟨
      { map := B
        δ_castSucc_castSucc_map := hg
        δ_succ_castSucc_map := ?_
        δ_succ_succ_map := ?_
        δ_map_of_lt := ?_
        δ_map_of_gt := ?_ }⟩⟩
    · have hCL : C ≠ L := by apply Fin.ne_of_val_ne; change i.val + 1 ≠ i.val; omega
      simpa [family] using hB C hCL
    · have hUL : U ≠ L := by apply Fin.ne_of_val_ne; change i.val + 1 + 1 ≠ i.val; omega
      have hUC : U ≠ C := by apply Fin.ne_of_val_ne; change i.val + 1 + 1 ≠ i.val + 1; omega
      simpa [family, hUC] using hB U hUL
    · intro j hj
      have hjL : j ≠ L := ne_of_lt hj
      have hjC : j ≠ C := by
        apply Fin.ne_of_val_ne
        change j.val < i.val at hj
        change j.val ≠ i.val + 1
        omega
      have hjU : j ≠ U := by
        apply Fin.ne_of_val_ne
        change j.val < i.val at hj
        change j.val ≠ i.val + 1 + 1
        omega
      simpa [family, hjC, hjU, e] using hB j hjL
    · intro j hj
      have hjU : j ≠ U := ne_of_gt hj
      have hjL : j ≠ L := by
        apply Fin.ne_of_val_ne
        change i.val + 1 + 1 < j.val at hj
        change j.val ≠ i.val
        omega
      have hjC : j ≠ C := by
        apply Fin.ne_of_val_ne
        change i.val + 1 + 1 < j.val at hj
        change j.val ≠ i.val + 1
        omega
      simpa [family, hjC, hjU, e] using hB j hjL
  have upper_inverse (g : X.PtSimplex (n + 2) x) (i : Fin (n + 2)) :
      Exists fun b : X.PtSimplex (n + 2) x =>
        Nonempty (SSet.PtSimplex.MulStruct b g e i) := by
    let U : Fin (n + 4) := i.succ.succ
    let family (j : Fin (n + 4)) (_ : j ≠ U) : X.PtSimplex (n + 2) x :=
      if j.val = i.val then g else e
    obtain ⟨B, b, hb, hB⟩ :=
      exists_kan_pointedSimplex_horn_filler X (n + 1) x U family
    refine ⟨b, ⟨
      { map := B
        δ_castSucc_castSucc_map := ?_
        δ_succ_castSucc_map := ?_
        δ_succ_succ_map := hb
        δ_map_of_lt := ?_
        δ_map_of_gt := ?_ }⟩⟩
    · have h : i.castSucc.castSucc ≠ U := by
        apply Fin.ne_of_val_ne
        change i.val ≠ i.val + 1 + 1
        omega
      simpa [family] using hB i.castSucc.castSucc h
    · have h : i.castSucc.succ ≠ U := by
        apply Fin.ne_of_val_ne
        change i.val + 1 ≠ i.val + 1 + 1
        omega
      simpa [family, e] using hB i.castSucc.succ h
    · intro j hj
      have hv : j.val < i.val := hj
      have hU : j ≠ U := by apply Fin.ne_of_val_ne; change j.val ≠ i.val + 1 + 1; omega
      simpa [family, ne_of_lt hv, e] using hB j hU
    · intro j hj
      have hv : i.val + 1 + 1 < j.val := hj
      have hU : j ≠ U := ne_of_gt hj
      have h0 : j.val ≠ i.val := by omega
      simpa [family, h0, e] using hB j hU
  have normalize_first
      (F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X)
      (a : Fin (n + 4) -> X.PtSimplex (n + 2) x)
      (ha : forall j : Fin (n + 4), SSet.stdSimplex.δ j ≫ F = (a j).map) :
      Exists fun F' : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X =>
        Exists fun a' : Fin (n + 4) -> X.PtSimplex (n + 2) x =>
          (forall j : Fin (n + 4), SSet.stdSimplex.δ j ≫ F' = (a' j).map) ∧
            a' 0 = e ∧ S a' = -S a := by
    choose b R using fun j : Fin (n + 4) =>
      left_factor (a j) (if j = 2 then a 1 else e) 0
    let M (j : Fin (n + 4)) := (R j).some
    have b_val (j : Fin (n + 4)) :
        v (b j) = (if j = 2 then v (a 1) else 0) - v (a j) := by
      have h := add_mul (a j) (b j) (if j = 2 then a 1 else e) 0 (M j)
      have hc : v (if j = 2 then a 1 else e) = if j = 2 then v (a 1) else 0 := by
        split_ifs <;> first | rfl | exact he
      rw [hc] at h
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.symm)
    let D (j : Fin (n + 5)) (hj : j ≠ (0 : Fin (n + 5))) :
        (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X :=
      if j.val = 1 then (SSet.PtSimplex.RelStruct.refl (a 1) 1).map else
      if j.val = 2 then F else (M (j.pred hj)).map
    have D_faces (j : Fin (n + 5)) (hj : j ≠ (0 : Fin (n + 5)))
        (t : Fin (n + 4)) :
        SSet.stdSimplex.δ t ≫ D j hj =
          if j.val = 1 then
            (if t.val = 1 then (a 1).map else if t.val = 2 then (a 1).map else SSet.const x) else
          if j.val = 2 then (a t).map else
            (if t.val = 0 then (b (j.pred hj)).map else
             if t.val = 1 then (if j.pred hj = 2 then (a 1).map else SSet.const x) else
             if t.val = 2 then (a (j.pred hj)).map else SSet.const x) := by
      dsimp only [D]
      by_cases h1 : j.val = 1
      · simp only [if_pos h1]
        simpa using rel_faces (a 1) 1 t
      simp only [if_neg h1]
      by_cases h2 : j.val = 2
      · simp only [if_pos h2]
        exact ha t
      simp only [if_neg h2]
      rw [mul_faces (a (j.pred hj)) (b (j.pred hj)) _ 0 (M (j.pred hj)) t]
      simp only [Fin.val_zero, zero_add]
      split_ifs <;> rfl
    have compat : SSet.horn.IsCompatible D := by
      intro j k hj hk hjk
      rw [D_faces j hj, D_faces k hk]
      have htwo : (2 : Fin (n + 4)).val = 2 := by
        change 2 % (n + 4) = 2
        exact Nat.mod_eq_of_lt (by omega)
      simp only [Fin.ext_iff, Fin.val_pred, Fin.castPred, Fin.val_castLT, htwo]
      have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
      have hjkv : j.val < k.val := hjk
      split_ifs <;> first
        | rfl
        | omega
        | (solve | simp [*])
        | (congr 2; apply Fin.ext;
            simp only [Fin.val_castLT, Fin.val_one]; omega)
    obtain ⟨H, hH⟩ := compat.exists_lift_of_kanComplex
    let a' (j : Fin (n + 4)) : X.PtSimplex (n + 2) x :=
      if j = 0 then e else if j = 1 then a 0 else b j
    have ha' (j : Fin (n + 4)) :
        SSet.stdSimplex.δ j ≫ SSet.stdSimplex.δ (0 : Fin (n + 5)) ≫ H = (a' j).map := by
      rw [← CosimplicialObject.δ_comp_δ''_assoc SSet.stdSimplex
        (show (0 : Fin (n + 5)) ≤ j.castSucc from Fin.zero_le _),
        hH j.succ (Fin.succ_ne_zero j), D_faces j.succ (Fin.succ_ne_zero j)]
      simp only [Fin.val_succ, Fin.val_castLT, Fin.val_zero, Fin.pred_succ]
      dsimp only [a']
      by_cases h0 : j = 0
      · subst j
        simp [e]
      by_cases h1 : j = 1
      · subst j
        simp
      have hv0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hv1 : j.val ≠ 1 := fun h => h1 (Fin.ext h)
      simp [h0, h1, show j.val + 1 ≠ 2 by omega]
    have value_change (j : Fin (n + 4)) :
        v (a' j) = -v (a j) + (if j = 0 then v (a 0) else 0) +
          (if j = 1 then v (a 0) + v (a 1) else 0) +
          (if j = 2 then v (a 1) else 0) := by
      have h02 : (0 : Fin (n + 4)) ≠ 2 := by
        apply Fin.ne_of_val_ne
        change (0 : Nat) ≠ 2
        decide
      have h12 : (1 : Fin (n + 4)) ≠ 2 := by
        apply Fin.ne_of_val_ne
        change (1 : Nat) ≠ 2
        decide
      by_cases h0 : j = 0
      · subst j
        simp [a', he, h02]
      by_cases h1 : j = 1
      · subst j
        simp [a', h12, add_comm, add_assoc]
      simp only [a', if_neg h0, if_neg h1, b_val, add_zero]
      split_ifs <;> simp [sub_eq_add_neg, add_comm]
    have hsum : S a' = -S a := by
      dsimp only [S]
      simp_rw [value_change, zsmul_add, zsmul_neg, smul_ite, zsmul_zero,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega), add_assoc, add_comm, add_left_comm]
    exact ⟨SSet.stdSimplex.δ (0 : Fin (n + 5)) ≫ H, a', ha', by simp [a'], hsum⟩
  have eliminate
      (F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X)
      (a : Fin (n + 4) -> X.PtSimplex (n + 2) x)
      (ha : forall j : Fin (n + 4), SSet.stdSimplex.δ j ≫ F = (a j).map)
      (k : Nat) (hk : k ≤ n)
      (hp : forall j : Fin (n + 4), j.val ≤ k -> a j = e) :
      Exists fun F' : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X =>
        Exists fun a' : Fin (n + 4) -> X.PtSimplex (n + 2) x =>
          (forall j : Fin (n + 4), SSet.stdSimplex.δ j ≫ F' = (a' j).map) ∧
            (forall j : Fin (n + 4), j.val ≤ k + 1 -> a' j = e) ∧ S a' = S a := by
    let p : Fin (n + 2) := ⟨k, by omega⟩
    let p1 : Fin (n + 4) := ⟨k + 1, by omega⟩
    let p2 : Fin (n + 4) := ⟨k + 2, by omega⟩
    obtain ⟨b, ⟨B⟩⟩ := upper_inverse (a p1) p
    obtain ⟨c, ⟨C⟩⟩ := exists_kan_mulStruct X (n + 1) x b (a p2) p
    have hb : v b = -v (a p1) := by
      have h := add_mul b (a p1) e p B
      rw [he] at h
      exact eq_neg_of_add_eq_zero_left h.symm
    have hc : v c = -v (a p1) + v (a p2) := by
      rw [add_mul b (a p2) c p C, hb]
    let q : Fin (n + 5) := ⟨k + 1, by omega⟩
    let d : Fin (n + 3) := ⟨k, by omega⟩
    let D (j : Fin (n + 5)) (_ : j ≠ q) :
        (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X :=
      if j.val = k then F else
      if j.val = k + 2 then B.map else
      if j.val = k + 3 then C.map else
      if h : k + 4 ≤ j.val then
        (SSet.PtSimplex.RelStruct.refl
          (a (j.pred (by apply Fin.ne_of_val_ne; change j.val ≠ 0; omega))) d).map
      else SSet.const x
    have D_faces (j : Fin (n + 5)) (hj : j ≠ q) (t : Fin (n + 4)) :
        SSet.stdSimplex.δ t ≫ D j hj =
          if j.val = k then (a t).map else
          if j.val = k + 2 then
            (if t.val = k then (a p1).map else
             if t.val = k + 1 then SSet.const x else
             if t.val = k + 2 then b.map else SSet.const x) else
          if j.val = k + 3 then
            (if t.val = k then (a p2).map else
             if t.val = k + 1 then c.map else
             if t.val = k + 2 then b.map else SSet.const x) else
          if h : k + 4 ≤ j.val then
            (if t.val = k then
              (a (j.pred (by apply Fin.ne_of_val_ne; change j.val ≠ 0; omega))).map else
             if t.val = k + 1 then
              (a (j.pred (by apply Fin.ne_of_val_ne; change j.val ≠ 0; omega))).map else
             SSet.const x) else SSet.const x := by
      dsimp only [D]
      by_cases h0 : j.val = k
      · simp only [if_pos h0]
        exact ha t
      simp only [if_neg h0]
      by_cases h2 : j.val = k + 2
      · simp only [if_pos h2]
        simpa only [p, e, SSet.RelativeMorphism.const_map] using mul_faces b (a p1) e p B t
      simp only [if_neg h2]
      by_cases h3 : j.val = k + 3
      · simp only [if_pos h3]
        exact mul_faces b (a p2) c p C t
      simp only [if_neg h3]
      by_cases h4 : k + 4 ≤ j.val
      · simp only [dif_pos h4]
        exact rel_faces _ d t
      · simp only [dif_neg h4, SSet.comp_const]
    have compat : SSet.horn.IsCompatible D := by
      intro j l hj hl hjl
      rw [D_faces j hj, D_faces l hl]
      simp only [Fin.val_pred, Fin.castPred, Fin.val_castLT]
      have hjq : j.val ≠ k + 1 := fun h => hj (Fin.ext h)
      have hlq : l.val ≠ k + 1 := fun h => hl (Fin.ext h)
      have hjlv : j.val < l.val := hjl
      split_ifs <;> first
        | rfl
        | omega
        | (rw [hp _ (by simp only [Fin.val_pred, Fin.val_castLT]; omega)]; rfl)
        | (solve | simp [*])
        | (simp only [*]; congr 2; apply Fin.ext;
            simp only [Fin.val_pred, p1, p2]; omega)
    obtain ⟨H, hH⟩ := compat.exists_lift_of_kanComplex
    let a' (j : Fin (n + 4)) : X.PtSimplex (n + 2) x :=
      if j = p1 then e else if j = p2 then c else a j
    have ha' (j : Fin (n + 4)) :
        SSet.stdSimplex.δ j ≫ SSet.stdSimplex.δ q ≫ H = (a' j).map := by
      by_cases hj : j.castSucc < q
      · have hjv : j.val < k + 1 := hj
        rw [CosimplicialObject.δ_comp_δ'_assoc SSet.stdSimplex hj,
          hH j.castSucc (ne_of_lt hj), D_faces j.castSucc (ne_of_lt hj)]
        simp only [Fin.val_castSucc, Fin.val_pred]
        dsimp only [q, a']
        have h1 : j ≠ p1 := by apply Fin.ne_of_val_ne; change j.val ≠ k + 1; omega
        have h2 : j ≠ p2 := by apply Fin.ne_of_val_ne; change j.val ≠ k + 2; omega
        simp only [if_neg h1, if_neg h2]
        split_ifs <;> first
          | rfl
          | omega
          | (rw [hp j (by omega)]; rfl)
          | (simp [*])
      · have hqj : q ≤ j.castSucc := le_of_not_gt hj
        have hjv : k + 1 ≤ j.val := hqj
        have hqs : q < j.succ := by change k + 1 < j.val + 1; omega
        rw [← CosimplicialObject.δ_comp_δ''_assoc SSet.stdSimplex hqj,
          hH j.succ (ne_of_gt hqs), D_faces j.succ (ne_of_gt hqs)]
        simp only [Fin.val_succ, Fin.val_castLT, Fin.pred_succ]
        dsimp only [q, a']
        simp only [Fin.ext_iff, p1, p2]
        split_ifs <;> first
          | rfl
          | omega
    have prefix' (j : Fin (n + 4)) (hj : j.val ≤ k + 1) : a' j = e := by
      dsimp only [a']
      by_cases h1 : j = p1
      · rw [if_pos h1]
      have hv1 : j.val ≠ k + 1 := fun h => h1 (Fin.ext h)
      have h2 : j ≠ p2 := by apply Fin.ne_of_val_ne; change j.val ≠ k + 2; omega
      rw [if_neg h1, if_neg h2, hp j (by omega)]
    have hp12 : p1 ≠ p2 := by apply Fin.ne_of_val_ne; change k + 1 ≠ k + 2; omega
    have value_change (j : Fin (n + 4)) :
        v (a' j) = v (a j) - (if j = p1 then v (a p1) else 0) -
          (if j = p2 then v (a p1) else 0) := by
      by_cases h1 : j = p1
      · subst j
        simp [a', he, hp12]
      by_cases h2 : j = p2
      · subst j
        simp [a', hc, hp12.symm, sub_eq_add_neg, add_comm]
      simp [a', h1, h2]
    have hsum : S a' = S a := by
      dsimp only [S]
      simp_rw [value_change, zsmul_sub, smul_ite, zsmul_zero, Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hsign : ((-1 : Int) ^ p2.val) • v (a p1) =
          -((-1 : Int) ^ p1.val) • v (a p1) := by
        simp [p1, p2, pow_succ]
      rw [hsign]
      simp
    exact ⟨SSet.stdSimplex.δ q ≫ H, a', ha', prefix', hsum⟩
  obtain ⟨F0, a0, ha0, hz0, hS0⟩ := normalize_first F a hfaces
  have reduce (k : Nat) (hk : k ≤ n + 1) :
      Exists fun F' : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X =>
        Exists fun a' : Fin (n + 4) -> X.PtSimplex (n + 2) x =>
          (forall j : Fin (n + 4), SSet.stdSimplex.δ j ≫ F' = (a' j).map) ∧
            (forall j : Fin (n + 4), j.val ≤ k -> a' j = e) ∧ S a' = S a0 := by
    induction k with
    | zero =>
      refine ⟨F0, a0, ha0, ?_, rfl⟩
      intro j hj
      have hj0 : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero hj)
      simpa only [hj0] using hz0
    | succ k ih =>
      obtain ⟨Fk, ak, hak, hpk, hSk⟩ := ih (by omega)
      obtain ⟨F', a', ha', hp', hS'⟩ := eliminate Fk ak hak k (by omega) hpk
      exact ⟨F', a', ha', hp', hS'.trans hSk⟩
  obtain ⟨Ff, af, haf, hpf, hSf⟩ := reduce (n + 1) le_rfl
  let i : Fin (n + 3) := Fin.last (n + 2)
  have R : SSet.PtSimplex.RelStruct (af i.castSucc) (af i.succ) i :=
    { map := Ff
      δ_castSucc_map := haf i.castSucc
      δ_succ_map := haf i.succ
      δ_map_of_lt := by
        intro j hj
        rw [haf j, hpf j (by change j.val < n + 2 at hj; omega)]
        rfl
      δ_map_of_gt := by
        intro j hj
        have hjv : n + 2 + 1 < j.val := hj
        have hjn := j.isLt
        omega }
  have hvf : v (af i.castSucc) = v (af i.succ) := hrel _ _ i R
  have hprefixsum :
      (∑ j : Fin (n + 2), ((-1 : Int) ^ j.val) • v (af j.castSucc.castSucc)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hpf _ (by change j.val ≤ n + 1; have := j.isLt; omega), he, zsmul_zero]
  have hfinal : S af = 0 := by
    dsimp only [S]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [hprefixsum, zero_add]
    change ((-1 : Int) ^ (n + 2)) • v (af i.castSucc) +
      ((-1 : Int) ^ (n + 3)) • v (af i.succ) = 0
    rw [hvf]
    simp [pow_succ]
  have hneg : -S a = 0 := hS0.symm.trans (hSf.symm.trans hfinal)
  exact neg_eq_zero.mp hneg

end Poincare.Topology
