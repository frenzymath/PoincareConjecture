import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped BigOperators

universe u v

namespace Poincare.Topology

theorem singular_one_cocycle_is_coboundary
    (X : TopCat.{u}) [SimplyConnectedSpace X]
    {A : Type v} [AddCommGroup A]
    (f : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 1)) -> A)
    (hf : forall s : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 2)),
      (∑ j : Fin 3, ((-1 : Int) ^ j.val) •
        f ((TopCat.toSSet.obj X).δ j s)) = 0) :
    Exists fun g : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 0)) -> A =>
      forall s : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk 1)),
        f s = g ((TopCat.toSSet.obj X).δ (0 : Fin 2) s) -
          g ((TopCat.toSSet.obj X).δ (1 : Fin 2) s) := by
  classical
  let Y := TopCat.toSSet.obj X
  let edge (F : C(stdSimplex Real (Fin 2), X)) : Y.obj (Opposite.op ⦋1⦌) :=
    (X.toSSetObjEquiv _).symm F
  let triangle (F : C(stdSimplex Real (Fin 3), X)) : Y.obj (Opposite.op ⦋2⦌) :=
    (X.toSSetObjEquiv _).symm F
  let e := stdSimplexHomeomorphUnitInterval
  have cocycle (s : Y.obj (Opposite.op ⦋2⦌)) :
      f (Y.δ 0 s) - f (Y.δ 1 s) + f (Y.δ 2 s) = 0 := by
    simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hf s
  have face_ext (F : C(stdSimplex Real (Fin 3), X)) (j : Fin 3)
      (G : C(stdSimplex Real (Fin 2), X))
      (h : forall z, F (stdSimplex.map j.succAbove z) = G z) :
      Y.δ j (triangle F) = edge G := by
    apply (X.toSSetObjEquiv _).injective
    ext z
    rw [TopCat.toSSetObjEquiv_δ_apply]
    simpa only [triangle, edge, Equiv.apply_symm_apply] using h z
  have constant_zero (a : X) : f (edge (ContinuousMap.const _ a)) = 0 := by
    have h (j : Fin 3) :
        Y.δ j (triangle (ContinuousMap.const _ a)) = edge (ContinuousMap.const _ a) :=
      face_ext _ j _ (fun _ => rfl)
    simpa only [h, sub_self, zero_add] using
      cocycle (triangle (ContinuousMap.const _ a))
  have cases_three (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have face_coord (j k : Fin 3) (z : stdSimplex Real (Fin 2)) :
      stdSimplex.map j.succAbove z k =
        if j = 0 then (![0, z 0, z 1] : Fin 3 -> Real) k else
        if j = 1 then (![z 0, 0, z 1] : Fin 3 -> Real) k else
          (![z 0, z 1, 0] : Fin 3 -> Real) k := by
    change FunOnFinite.linearMap Real Real j.succAbove z k = _
    rw [FunOnFinite.linearMap_apply_apply]
    change (Finset.univ.filter (fun x : Fin 2 => j.succAbove x = k)).sum
      (fun x : Fin 2 => z.val x) = _
    rw [Finset.sum_filter, Fin.sum_univ_two]
    rcases cases_three j with rfl | rfl | rfl <;>
      rcases cases_three k with rfl | rfl | rfl <;>
      norm_num [Matrix.cons_val_two, Fin.succAbove,
        show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        show ¬(2 : Fin 3) ≤ 1 by decide, show (0 : Fin 3) < 2 by decide,
        show (1 : Fin 3) < 2 by decide] <;> rfl
  let E {a b : X} (p : Path a b) : Y.obj (Opposite.op ⦋1⦌) :=
    edge (p.toContinuousMap.comp ⟨e, e.continuous⟩)
  let I {a b : X} (p : Path a b) : A := f (E p)

  have composition {a b c : X} (p : Path a b) (q : Path b c) :
      I (p.trans q) = I p + I q := by
    let T : C(stdSimplex Real (Fin 3), X) :=
      ⟨fun z => (p.trans q).extend (z 1 / 2 + z 2),
        (p.trans q).continuous_extend.comp
          ((((continuous_apply 1).comp continuous_subtype_val).div_const 2).add
            ((continuous_apply 2).comp continuous_subtype_val))⟩
    have h0 : Y.δ 0 (triangle T) = E q := by
      apply face_ext T 0 _
      intro z
      change (p.trans q).extend
        (stdSimplex.map (0 : Fin 3).succAbove z 1 / 2 +
          stdSimplex.map (0 : Fin 3).succAbove z 2) = q (e z)
      rw [face_coord, face_coord]
      norm_num [Matrix.cons_val_two, Fin.ext_iff]
      have hz := stdSimplex.add_eq_one z
      have hz1 : 0 ≤ z 1 := z.property.1 1
      rw [Path.extend_trans_of_half_le p q (by linarith)]
      have harg : 2 * (z 0 / 2 + z 1) - 1 = z 1 := by linarith
      rw [harg]
      exact Path.extend_extends' q (e z)
    have h1 : Y.δ 1 (triangle T) = E (p.trans q) := by
      apply face_ext T 1 _
      intro z
      change (p.trans q).extend
        (stdSimplex.map (1 : Fin 3).succAbove z 1 / 2 +
          stdSimplex.map (1 : Fin 3).succAbove z 2) = (p.trans q) (e z)
      rw [face_coord, face_coord]
      norm_num [Matrix.cons_val_two, Fin.ext_iff]
      rfl
    have h2 : Y.δ 2 (triangle T) = E p := by
      apply face_ext T 2 _
      intro z
      change (p.trans q).extend
        (stdSimplex.map (2 : Fin 3).succAbove z 1 / 2 +
          stdSimplex.map (2 : Fin 3).succAbove z 2) = p (e z)
      rw [face_coord, face_coord]
      norm_num [Matrix.cons_val_two, Fin.ext_iff]
      rw [Path.extend_trans_of_le_half p q (by have := stdSimplex.le_one z 1; linarith)]
      have harg : 2 * (z 1 / 2) = z 1 := by linarith
      rw [harg]
      exact Path.extend_extends' p (e z)
    have h := cocycle (triangle T)
    rw [h0, h1, h2] at h
    change I q - I (p.trans q) + I p = 0 at h
    apply sub_eq_zero.mp
    calc
      I (p.trans q) - (I p + I q) = -(I q - I (p.trans q) + I p) := by abel
      _ = 0 := by rw [h, neg_zero]

  have homotopy_value {a b : X} {p q : Path a b} (H : p.Homotopy q) : I p = I q := by
    let t (z : stdSimplex Real (Fin 3)) : unitInterval :=
      ⟨z 2, z.property.1 2, stdSimplex.le_one z 2⟩
    let s (z : stdSimplex Real (Fin 3)) : unitInterval :=
      ⟨z 1 + z 2, add_nonneg (z.property.1 1) (z.property.1 2), by
        change z.val 1 + z.val 2 ≤ 1
        have hz : z.val 0 + z.val 1 + z.val 2 = 1 := by
          simpa [Fin.sum_univ_succ, add_assoc] using z.property.2
        have hz0 : 0 ≤ z.val 0 := z.property.1 0
        linarith⟩
    have t_continuous : Continuous t :=
      ((continuous_apply 2).comp continuous_subtype_val).subtype_mk _
    have s_continuous : Continuous s :=
      (((continuous_apply 1).comp continuous_subtype_val).add
        ((continuous_apply 2).comp continuous_subtype_val)).subtype_mk _
    let T0 : C(stdSimplex Real (Fin 3), X) :=
      ⟨fun z => H (s z, t z), by fun_prop⟩
    let T1 : C(stdSimplex Real (Fin 3), X) :=
      ⟨fun z => H (t z, s z), by fun_prop⟩
    let L : C(stdSimplex Real (Fin 2), X) := ⟨fun z => H (e z, e z), by fun_prop⟩
    have t_face (j : Fin 3) (z : stdSimplex Real (Fin 2)) :
        t (stdSimplex.map j.succAbove z) = if j = 2 then 0 else e z := by
      apply Subtype.ext
      change stdSimplex.map j.succAbove z 2 = _
      rw [face_coord]
      rcases cases_three j with rfl | rfl | rfl <;>
        norm_num [e, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
          Matrix.cons_val_two, Fin.ext_iff] <;> rfl
    have s_face (j : Fin 3) (z : stdSimplex Real (Fin 2)) :
        s (stdSimplex.map j.succAbove z) = if j = 0 then 1 else e z := by
      apply Subtype.ext
      change stdSimplex.map j.succAbove z 1 + stdSimplex.map j.succAbove z 2 = _
      rw [face_coord, face_coord]
      rcases cases_three j with rfl | rfl | rfl <;>
        norm_num [e, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
          Matrix.cons_val_two, Fin.ext_iff]
      all_goals
        first
        | exact stdSimplex.add_eq_one z
        | rfl
    have h00 : Y.δ 0 (triangle T0) = E q := by
      apply face_ext T0 0 _
      intro z
      change H (s (stdSimplex.map (0 : Fin 3).succAbove z),
        t (stdSimplex.map (0 : Fin 3).succAbove z)) = q (e z)
      rw [s_face, t_face]
      simp [show (0 : Fin 3) ≠ 2 by decide]
    have h01 : Y.δ 1 (triangle T0) = edge L := by
      apply face_ext T0 1 _
      intro z
      change H (s (stdSimplex.map (1 : Fin 3).succAbove z),
        t (stdSimplex.map (1 : Fin 3).succAbove z)) = H (e z, e z)
      rw [s_face, t_face]
      simp [show (1 : Fin 3) ≠ 2 by decide]
    have h02 : Y.δ 2 (triangle T0) = edge (ContinuousMap.const _ a) := by
      apply face_ext T0 2 _
      intro z
      change H (s (stdSimplex.map (2 : Fin 3).succAbove z),
        t (stdSimplex.map (2 : Fin 3).succAbove z)) = a
      rw [s_face, t_face]
      simp [show (2 : Fin 3) ≠ 0 by decide]
    have h10 : Y.δ 0 (triangle T1) = edge (ContinuousMap.const _ b) := by
      apply face_ext T1 0 _
      intro z
      change H (t (stdSimplex.map (0 : Fin 3).succAbove z),
        s (stdSimplex.map (0 : Fin 3).succAbove z)) = b
      rw [t_face, s_face]
      simp [show (0 : Fin 3) ≠ 2 by decide]
    have h11 : Y.δ 1 (triangle T1) = edge L := by
      apply face_ext T1 1 _
      intro z
      change H (t (stdSimplex.map (1 : Fin 3).succAbove z),
        s (stdSimplex.map (1 : Fin 3).succAbove z)) = H (e z, e z)
      rw [t_face, s_face]
      simp [show (1 : Fin 3) ≠ 2 by decide]
    have h12 : Y.δ 2 (triangle T1) = E p := by
      apply face_ext T1 2 _
      intro z
      change H (t (stdSimplex.map (2 : Fin 3).succAbove z),
        s (stdSimplex.map (2 : Fin 3).succAbove z)) = p (e z)
      rw [t_face, s_face]
      simp [show (2 : Fin 3) ≠ 0 by decide]
    have h0 := cocycle (triangle T0)
    have h1 := cocycle (triangle T1)
    rw [h00, h01, h02, constant_zero, add_zero] at h0
    rw [h10, h11, h12, constant_zero, zero_sub] at h1
    have hq : I q = f (edge L) := sub_eq_zero.mp h0
    have hp : I p = f (edge L) := by
      simpa only [neg_neg] using eq_neg_of_add_eq_zero_right h1
    exact hp.trans hq.symm
  have face_vertex (r : Y.obj (Opposite.op ⦋1⦌)) (j : Fin 2) :
      TopCat.toSSetObj₀Equiv (Y.δ j r) =
        X.toSSetObjEquiv _ r (e.symm (if j = 0 then 1 else 0)) := by
    change (X.toSSetObjEquiv _ (Y.δ j r)) default = _
    rw [TopCat.toSSetObjEquiv_δ_apply]
    congr 1
    rw [show (default : stdSimplex Real (Fin 1)) = stdSimplex.vertex 0 from
      Subsingleton.elim _ _, stdSimplex.map_vertex]
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl <;> apply e.injective <;>
      norm_num [e, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc, Fin.succAbove]
  let b : X := Classical.choice (inferInstance : Nonempty X)
  let paths (x : X) : Path b x := PathConnectedSpace.somePath b x
  let g (x : Y.obj (Opposite.op ⦋0⦌)) : A := I (paths (TopCat.toSSetObj₀Equiv x))
  refine ⟨g, ?_⟩
  intro r
  let F := X.toSSetObjEquiv _ r
  let p : Path (TopCat.toSSetObj₀Equiv (Y.δ 1 r))
      (TopCat.toSSetObj₀Equiv (Y.δ 0 r)) :=
    { toFun := fun t => F (e.symm t)
      continuous_toFun := by fun_prop
      source' := by simpa using (face_vertex r 1).symm
      target' := by simpa using (face_vertex r 0).symm }
  have hp : E p = r := by
    apply (X.toSSetObjEquiv _).injective
    ext z
    simp only [E, edge, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
    change F (e.symm (e z)) = F z
    rw [e.symm_apply_apply]
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic
    ((paths (TopCat.toSSetObj₀Equiv (Y.δ 1 r))).trans p)
    (paths (TopCat.toSSetObj₀Equiv (Y.δ 0 r)))
  have h := homotopy_value H
  rw [composition] at h
  change g (Y.δ 1 r) + f (E p) = g (Y.δ 0 r) at h
  rw [hp] at h
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)

end Poincare.Topology
