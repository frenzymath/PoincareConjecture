import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct








set_option autoImplicit false

open CategoryTheory Simplicial

universe u

namespace Poincare.Topology


theorem exists_pointedSimplex_of_constant_faces (X : SSet.{u}) (n : Nat)
    (x : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 1))) ⟶ X)
    (hF : forall j : Fin (n + 2), SSet.stdSimplex.δ j ≫ F = SSet.const x) :
    Exists fun f : X.PtSimplex (n + 1) x => f.map = F := by
  refine ⟨{ map := F, comm := ?_ }, rfl⟩
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι, hF]
  rfl


theorem pointedSimplex_horn_compatible (X : SSet.{u}) (n : Nat)
    (x : X.obj (Opposite.op (SimplexCategory.mk 0))) (i : Fin (n + 3))
    (f : forall j : Fin (n + 3), Ne j i -> X.PtSimplex (n + 1) x) :
    SSet.horn.IsCompatible (fun j hj => (f j hj).map) := by
  intro j k hj hk hjk
  rw [SSet.PtSimplex.δ_map, SSet.PtSimplex.δ_map]


theorem exists_kan_pointedSimplex_horn_filler (X : SSet.{u}) [SSet.KanComplex X]
    (n : Nat) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) (i : Fin (n + 3))
    (f : forall j : Fin (n + 3), Ne j i -> X.PtSimplex (n + 1) x) :
    Exists fun F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ X =>
      Exists fun g : X.PtSimplex (n + 1) x =>
        And (SSet.stdSimplex.δ i ≫ F = g.map)
          (forall (j : Fin (n + 3)) (hj : Ne j i), SSet.stdSimplex.δ j ≫ F = (f j hj).map) := by
  obtain ⟨F, hF⟩ := (pointedSimplex_horn_compatible X n x i f).exists_lift_of_kanComplex
  have hi (l : Fin (n + 2)) :
      SSet.stdSimplex.δ l ≫ SSet.stdSimplex.δ i ≫ F = SSet.const x := by
    by_cases hli : l.castSucc < i
    · rw [CosimplicialObject.δ_comp_δ'_assoc SSet.stdSimplex hli,
        hF l.castSucc (ne_of_lt hli), SSet.PtSimplex.δ_map]
    · have hil : i ≤ l.castSucc := le_of_not_gt hli
      have his : i < l.succ :=
        lt_of_le_of_lt hil (Fin.castSucc_lt_succ_iff.mpr le_rfl)
      rw [← CosimplicialObject.δ_comp_δ''_assoc SSet.stdSimplex hil,
        hF l.succ (ne_of_gt his), SSet.PtSimplex.δ_map]
  obtain ⟨g, hg⟩ := exists_pointedSimplex_of_constant_faces X n x
    (SSet.stdSimplex.δ i ≫ F) hi
  exact ⟨F, g, hg.symm, hF⟩


theorem exists_kan_mulStruct (X : SSet.{u}) [SSet.KanComplex X] (n : Nat)
    (x : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (f g : X.PtSimplex (n + 1) x) (i : Fin (n + 1)) :
    Exists fun fg : X.PtSimplex (n + 1) x => Nonempty (SSet.PtSimplex.MulStruct f g fg i) := by
  let L : Fin (n + 3) := i.castSucc.castSucc
  let C : Fin (n + 3) := i.castSucc.succ
  let U : Fin (n + 3) := i.succ.succ
  have hLC : L < C := Fin.castSucc_lt_succ_iff.mpr le_rfl
  have hCU : C < U := by
    change i.val + 1 < i.val + 1 + 1
    exact Nat.lt_succ_self _
  let family (j : Fin (n + 3)) (_ : j ≠ C) : X.PtSimplex (n + 1) x :=
    if j = L then g else if j = U then f else SSet.RelativeMorphism.const
  obtain ⟨F, fg, hfg, hF⟩ := exists_kan_pointedSimplex_horn_filler X n x C family
  refine ⟨fg, ⟨{ map := F
                 δ_castSucc_castSucc_map := ?_
                 δ_succ_castSucc_map := hfg
                 δ_succ_succ_map := ?_
                 δ_map_of_lt := ?_
                 δ_map_of_gt := ?_ }⟩⟩
  · have h := hF L (ne_of_lt hLC)
    dsimp only [family] at h
    rw [if_pos rfl] at h
    exact h
  · have h := hF U (ne_of_gt hCU)
    dsimp only [family] at h
    rw [if_neg (ne_of_gt (hLC.trans hCU)), if_pos rfl] at h
    exact h
  · intro j hj
    have hjL : j ≠ L := ne_of_lt hj
    have hjC : j ≠ C := ne_of_lt (hj.trans hLC)
    have hjU : j ≠ U := ne_of_lt ((hj.trans hLC).trans hCU)
    have h := hF j hjC
    dsimp only [family] at h
    rw [if_neg hjL, if_neg hjU] at h
    exact h
  · intro j hj
    have hjU : j ≠ U := ne_of_gt hj
    have hjC : j ≠ C := ne_of_gt (hCU.trans hj)
    have hjL : j ≠ L := ne_of_gt (hLC.trans (hCU.trans hj))
    have h := hF j hjC
    dsimp only [family] at h
    rw [if_neg hjL, if_neg hjU] at h
    exact h

end Poincare.Topology
