import PoincareConjecture.Proofs.M02.Topology.PointedHorn
import Mathlib.Algebra.Group.Basic

set_option autoImplicit false

open CategoryTheory Simplicial

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

set_option maxHeartbeats 1000000 in

theorem pointedSimplex_additive_mulStruct
    (X : SSet.{u}) [SSet.KanComplex X] (n : Nat)
    (x : X.obj (Opposite.op (SimplexCategory.mk 0)))
    {A : Type v} [AddCommGroup A]
    (v : X.PtSimplex (n + 2) x -> A)
    (hzero : v SSet.RelativeMorphism.const = 0)
    (hmul : forall (f g c : X.PtSimplex (n + 2) x),
      SSet.PtSimplex.MulStruct f g c (0 : Fin (n + 2)) ->
        v c = v f + v g)
    (f g c : X.PtSimplex (n + 2) x) (i : Fin (n + 2))
    (r : SSet.PtSimplex.MulStruct f g c i) :
    v c = v f + v g := by
  classical
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
  have all_indices (i : Fin (n + 2)) :
      forall (f g c : X.PtSimplex (n + 2) x),
        SSet.PtSimplex.MulStruct f g c i -> v c = v f + v g := by
    induction i using Fin.induction with
    | zero => exact hmul
    | succ i ih =>
      intro f g c r
      let p : Fin (n + 2) := i.castSucc
      let U : Fin (n + 4) := p.succ.succ
      let faces (j : Fin (n + 4)) (_ : j ≠ U) : X.PtSimplex (n + 2) x :=
        if j.val = i.val then g else SSet.RelativeMorphism.const
      obtain ⟨B, b, hb, hB⟩ :=
        exists_kan_pointedSimplex_horn_filler X (n + 1) x U faces
      have B_faces (j : Fin (n + 4)) :
          SSet.stdSimplex.δ j ≫ B =
            if j.val = i.val then g.map else
            if j.val = i.val + 2 then b.map else SSet.const x := by
        by_cases hj : j = U
        · subst j
          simpa [U, p, Nat.add_assoc] using hb
        · rw [hB j hj]
          have h2 : j.val ≠ i.val + 2 := by
            intro h
            apply hj
            exact Fin.ext h
          dsimp only [faces]
          rw [if_neg h2]
          split_ifs <;> rfl
      have rb : SSet.PtSimplex.MulStruct b g SSet.RelativeMorphism.const p :=
        { map := B
          δ_castSucc_castSucc_map := by simp [B_faces, p]
          δ_succ_castSucc_map := by simp [B_faces, p]
          δ_succ_succ_map := by simp [B_faces, p, Nat.add_assoc]
          δ_map_of_lt := by
            intro j hj
            change j.val < i.val at hj
            rw [B_faces]
            split_ifs <;> first | rfl | omega
          δ_map_of_gt := by
            intro j hj
            change i.val + 1 + 1 < j.val at hj
            rw [B_faces]
            split_ifs <;> first | rfl | omega }
      have hb0 : v b + v g = 0 := (ih b g _ rb).symm.trans hzero
      let q : Fin (n + 5) := ⟨i.val + 3, by omega⟩
      let l : Fin (n + 3) := ⟨i.val, by omega⟩
      let u : Fin (n + 3) := ⟨i.val + 2, by omega⟩
      let D (j : Fin (n + 5)) (_ : j ≠ q) :
          (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ X :=
        if j.val = i.val then r.map else
        if j.val = i.val + 1 then (SSet.PtSimplex.RelStruct.refl f u).map else
        if j.val = i.val + 2 then B else
        if j.val = i.val + 4 then (SSet.PtSimplex.RelStruct.refl f l).map else SSet.const x
      have D_faces (j : Fin (n + 5)) (hj : j ≠ q) (k : Fin (n + 4)) :
          SSet.stdSimplex.δ k ≫ D j hj =
            if j.val = i.val then
              (if k.val = i.val + 1 then g.map else
               if k.val = i.val + 2 then c.map else
               if k.val = i.val + 3 then f.map else SSet.const x) else
            if j.val = i.val + 1 then
              (if k.val = i.val + 2 then f.map else
               if k.val = i.val + 3 then f.map else SSet.const x) else
            if j.val = i.val + 2 then
              (if k.val = i.val then g.map else
               if k.val = i.val + 2 then b.map else SSet.const x) else
            if j.val = i.val + 4 then
              (if k.val = i.val then f.map else
               if k.val = i.val + 1 then f.map else SSet.const x) else SSet.const x := by
        dsimp only [D]
        by_cases h0 : j.val = i.val
        · simp only [if_pos h0]
          simpa only [Fin.val_succ, Nat.add_assoc] using mul_faces f g c i.succ r k
        simp only [if_neg h0]
        by_cases h1 : j.val = i.val + 1
        · simp only [if_pos h1]
          simpa only [u, Nat.add_assoc] using rel_faces f u k
        simp only [if_neg h1]
        by_cases h2 : j.val = i.val + 2
        · simp only [if_pos h2]
          exact B_faces k
        simp only [if_neg h2]
        by_cases h4 : j.val = i.val + 4
        · simp only [if_pos h4]
          exact rel_faces f l k
        simp only [if_neg h4, SSet.comp_const]
      have compat : SSet.horn.IsCompatible D := by
        intro j k hj hk hjk
        rw [D_faces j hj, D_faces k hk]
        simp only [Fin.val_pred, Fin.castPred, Fin.val_castLT]
        change j.val < k.val at hjk
        have hjq : j.val ≠ i.val + 3 := fun h => hj (Fin.ext h)
        have hkq : k.val ≠ i.val + 3 := fun h => hk (Fin.ext h)
        split_ifs <;> first | rfl | omega | (simp [*])
      obtain ⟨H, hH⟩ := compat.exists_lift_of_kanComplex
      have Z_faces (j : Fin (n + 4)) :
          SSet.stdSimplex.δ j ≫ SSet.stdSimplex.δ q ≫ H =
            if j.val = i.val then c.map else
            if j.val = i.val + 1 then f.map else
            if j.val = i.val + 2 then b.map else SSet.const x := by
        by_cases hj : j.castSucc < q
        · have hjv : j.val < i.val + 3 := hj
          rw [CosimplicialObject.δ_comp_δ'_assoc SSet.stdSimplex hj,
            hH j.castSucc (ne_of_lt hj), D_faces j.castSucc (ne_of_lt hj)]
          simp only [Fin.val_castSucc, Fin.val_pred]
          dsimp only [q]
          split_ifs <;> first | rfl | omega
        · have hqj : q ≤ j.castSucc := le_of_not_gt hj
          have hqjv : i.val + 3 ≤ j.val := hqj
          have hqs : q < j.succ := by
            change i.val + 3 < j.val + 1
            omega
          rw [← CosimplicialObject.δ_comp_δ''_assoc SSet.stdSimplex hqj,
            hH j.succ (ne_of_gt hqs), D_faces j.succ (ne_of_gt hqs)]
          simp only [Fin.val_succ, Fin.val_castLT]
          dsimp only [q]
          split_ifs <;> first | rfl | omega
      have rc : SSet.PtSimplex.MulStruct b c f p :=
        { map := SSet.stdSimplex.δ q ≫ H
          δ_castSucc_castSucc_map := by simp [Z_faces, p]
          δ_succ_castSucc_map := by simp [Z_faces, p]
          δ_succ_succ_map := by simp [Z_faces, p, Nat.add_assoc]
          δ_map_of_lt := by
            intro j hj
            change j.val < i.val at hj
            rw [Z_faces]
            split_ifs <;> first | rfl | omega
          δ_map_of_gt := by
            intro j hj
            change i.val + 1 + 1 < j.val at hj
            rw [Z_faces]
            split_ifs <;> first | rfl | omega }
      have hc : v f = v b + v c := ih b c f rc
      calc
        v c = (v b + v g) + v c := by rw [hb0, zero_add]
        _ = (v b + v c) + v g := add_right_comm _ _ _
        _ = v f + v g := by rw [← hc]
  exact all_indices i f g c r

end PoincareConjecture.Proofs.M02.Topology
