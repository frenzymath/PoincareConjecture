import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.FoldCubeCoordinates







set_option autoImplicit false

universe u

namespace Poincare.Topology


theorem stdSimplex_central_face_homotopicRel_transAt {X : Type u} [TopologicalSpace X]
    (n : Nat)
    (q : C((Fin (n + 1) -> unitInterval), stdSimplex Real (Fin (n + 2))))
    (hq0 : forall t, q t 0 = ∏ k : Fin (n + 1), (1 - (t k : Real)))
    (hqs : forall t (j : Fin (n + 1)), q t j.succ =
      (t j : Real) * ∏ k : Fin (n + 1), if j < k then 1 - (t k : Real) else 1)
    (F : C(stdSimplex Real (Fin (n + 3)), X)) (x : X)
    (hF : forall j : Fin (n + 3), Ne j 0 -> Ne j 1 -> Ne j 2 ->
      forall z : stdSimplex Real (Fin (n + 2)), F (stdSimplex.map j.succAbove z) = x)
    (f g : GenLoop (Fin (n + 1)) X x)
    (hf : f.val = (F.comp (ContinuousMap.mk
      (stdSimplex.map (2 : Fin (n + 3)).succAbove) (stdSimplex.continuous_map _))).comp q)
    (hg : g.val = (F.comp (ContinuousMap.mk
      (stdSimplex.map (0 : Fin (n + 3)).succAbove) (stdSimplex.continuous_map _))).comp q) :
    ContinuousMap.HomotopicRel
      ((F.comp (ContinuousMap.mk (stdSimplex.map (1 : Fin (n + 3)).succAbove)
        (stdSimplex.continuous_map _))).comp q)
      (GenLoop.transAt (0 : Fin (n + 1)) f g).val
      (Cube.boundary (Fin (n + 1))) := by
  obtain ⟨w, hw0, hw1, hw2, hws⟩ := exists_stdSimplex_three_face_fold n
  obtain ⟨H⟩ := stdSimplex_three_face_fold_homotopicRel n w hw0 hw1 hw2 hws F x hF
  have hterminal : (F.comp w).comp q = (GenLoop.transAt (0 : Fin (n + 1)) f g).val := by
    ext z
    change F (w (q z)) = if (z 0 : Real) ≤ 1 / 2
      then f (Function.update z 0 (Set.projIcc 0 1 zero_le_one (2 * (z 0 : Real))))
      else g (Function.update z 0 (Set.projIcc 0 1 zero_le_one (2 * (z 0 : Real) - 1)))
    split_ifs with hz
    · have ha : 2 * (z 0 : Real) ∈ unitInterval :=
        (unitInterval.mul_pos_mem_iff zero_lt_two).mpr ⟨(z 0).property.1, hz⟩
      let a : unitInterval := ⟨2 * (z 0 : Real), ha⟩
      have hw := stdSimplex_three_face_fold_cube_first n q hq0 hqs w hw0 hw1 hw2 hws
        (z 0) a (Fin.tail z) rfl
      rw [Fin.cons_self_tail] at hw
      rw [hw, Set.projIcc_of_mem zero_le_one ha]
      have hu : Function.update z 0 a = Fin.cons a (Fin.tail z) := by
        rw [← Fin.cons_self_tail z, Fin.update_cons_zero]
        rfl
      change F (stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a (Fin.tail z)))) =
        f (Function.update z 0 a)
      rw [hu]
      change _ = f.val _
      rw [hf]
      rfl
    · have ha : 2 * (z 0 : Real) - 1 ∈ unitInterval :=
        unitInterval.two_mul_sub_one_mem_iff.mpr ⟨(lt_of_not_ge hz).le, (z 0).property.2⟩
      let a : unitInterval := ⟨2 * (z 0 : Real) - 1, ha⟩
      have hw := stdSimplex_three_face_fold_cube_second n q hq0 hqs w hw0 hw1 hw2 hws
        (z 0) a (Fin.tail z) rfl
      rw [Fin.cons_self_tail] at hw
      rw [hw, Set.projIcc_of_mem zero_le_one ha]
      have hu : Function.update z 0 a = Fin.cons a (Fin.tail z) := by
        rw [← Fin.cons_self_tail z, Fin.update_cons_zero]
        rfl
      change F (stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a (Fin.tail z)))) =
        g (Function.update z 0 a)
      rw [hu]
      change _ = g.val _
      rw [hg]
      rfl
  rw [← hterminal]
  exact ⟨{
    toHomotopy := H.toHomotopy.compContinuousMap q
    prop' := fun s z hz => H.eq_fst s
      ((stdSimplex_cube_coordinates_boundary_iff (n + 1) q hq0 hqs z).mpr hz) }⟩

end Poincare.Topology
