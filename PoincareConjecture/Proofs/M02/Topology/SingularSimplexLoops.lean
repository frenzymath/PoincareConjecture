import PoincareConjecture.Proofs.M02.Topology.SimplexFaceHomotopy
import PoincareConjecture.Proofs.M02.Topology.SimplexCubeConcatenation









set_option autoImplicit false

open CategoryTheory Simplicial

universe u

namespace PoincareConjecture.Proofs.M02.Topology


theorem singular_pointedSimplex_boundary (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a : (TopCat.toSSet.obj X).PtSimplex (n + 1) x)
    (z : stdSimplex Real (Fin (n + 2)))
    (hz : Exists fun j : Fin (n + 2) => z j = 0) :
    X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map) z = TopCat.toSSetObj₀Equiv x := by
  obtain ⟨j, hj⟩ := hz
  obtain ⟨y, rfl⟩ := (stdSimplex_face_range_iff n j z).mpr hj
  have h := congrArg (fun G : (Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj X =>
    X.toSSetObjEquiv _ (SSet.yonedaEquiv G) y) (a.δ_map j)
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply,
    singular_const_apply] at h
  exact h


theorem exists_singular_pointedSimplex_genLoop (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a : (TopCat.toSSet.obj X).PtSimplex (n + 1) x)
    (q : C((Fin (n + 1) -> unitInterval), stdSimplex Real (Fin (n + 2))))
    (hq : forall t, t ∈ Cube.boundary (Fin (n + 1)) ->
      Exists fun j : Fin (n + 2) => q t j = 0) :
    Exists fun f : GenLoop (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x) =>
      f.val = (X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map)).comp q := by
  exact ⟨⟨(X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map)).comp q,
    fun t ht => singular_pointedSimplex_boundary X n x a (q t) (hq t ht)⟩, rfl⟩


theorem singular_relStruct_genLoop_homotopic (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a b : (TopCat.toSSet.obj X).PtSimplex n x) (i : Fin (n + 1))
    (r : SSet.PtSimplex.RelStruct a b i)
    (q : C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))))
    (hq : forall t, t ∈ Cube.boundary (Fin n) ->
      Exists fun j : Fin (n + 1) => q t j = 0)
    (f g : GenLoop (Fin n) X (TopCat.toSSetObj₀Equiv x))
    (hf : f.val = (X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map)).comp q)
    (hg : g.val = (X.toSSetObjEquiv _ (SSet.yonedaEquiv b.map)).comp q) :
    GenLoop.Homotopic f g := by
  obtain ⟨H⟩ := singular_relStruct_homotopicRel X n x a b i r
  change ContinuousMap.HomotopicRel f.val g.val (Cube.boundary (Fin n))
  rw [hf, hg]
  exact ⟨{ toHomotopy := H.toHomotopy.compContinuousMap q
           prop' := fun s t ht => H.eq_fst s (hq t ht) }⟩


theorem singular_mulStruct_genLoop_mul (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a b c : (TopCat.toSSet.obj X).PtSimplex (n + 2) x)
    (r : SSet.PtSimplex.MulStruct a b c (0 : Fin (n + 2)))
    (q : C((Fin (n + 2) -> unitInterval), stdSimplex Real (Fin (n + 3))))
    (hq0 : forall t, q t 0 = ∏ k : Fin (n + 2), (1 - (t k : Real)))
    (hqs : forall t (j : Fin (n + 2)), q t j.succ =
      (t j : Real) * ∏ k : Fin (n + 2), if j < k then 1 - (t k : Real) else 1)
    (f g h : GenLoop (Fin (n + 2)) X (TopCat.toSSetObj₀Equiv x))
    (hf : f.val = (X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map)).comp q)
    (hg : g.val = (X.toSSetObjEquiv _ (SSet.yonedaEquiv b.map)).comp q)
    (hh : h.val = (X.toSSetObjEquiv _ (SSet.yonedaEquiv c.map)).comp q) :
    (Quotient.mk _ h : HomotopyGroup (Fin (n + 2)) X (TopCat.toSSetObj₀Equiv x)) =
      ((· * ·) : _ -> _ -> HomotopyGroup (Fin (n + 2)) X (TopCat.toSSetObj₀Equiv x))
        (Quotient.mk _ f) (Quotient.mk _ g) := by
  let F := X.toSSetObjEquiv _ (SSet.yonedaEquiv r.map)
  have hface (j : Fin (n + 4)) (d : (TopCat.toSSet.obj X).PtSimplex (n + 2) x)
      (hd : SSet.stdSimplex.δ j ≫ r.map = d.map) :
      F.comp ⟨stdSimplex.map j.succAbove, stdSimplex.continuous_map _⟩ =
        X.toSSetObjEquiv _ (SSet.yonedaEquiv d.map) := by
    ext z
    have hz := congrArg (fun G : (Δ[n + 2] : SSet.{u}) ⟶ TopCat.toSSet.obj X =>
      X.toSSetObjEquiv _ (SSet.yonedaEquiv G) z) hd
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply] at hz
    exact hz
  have hF (j : Fin (n + 4)) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj2 : j ≠ 2)
      (z : stdSimplex Real (Fin (n + 3))) :
      F (stdSimplex.map j.succAbove z) = TopCat.toSSetObj₀Equiv x := by
    have hj0' : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    have hj1' : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
    have hj2' : j.val ≠ 2 := fun h => hj2 (Fin.ext h)
    have hgt : (0 : Fin (n + 2)).succ.succ < j := by
      change (0 : Fin (n + 2)).val + 1 + 1 < j.val
      rw [Fin.val_zero]
      have hpos : 0 < j.val := Nat.pos_of_ne_zero hj0'
      have hgt1 : 1 < j.val := lt_of_le_of_ne (Nat.succ_le_of_lt hpos) hj1'.symm
      exact lt_of_le_of_ne (Nat.succ_le_of_lt hgt1) hj2'.symm
    have hz := congrArg (fun G : (Δ[n + 2] : SSet.{u}) ⟶ TopCat.toSSet.obj X =>
      X.toSSetObjEquiv _ (SSet.yonedaEquiv G) z) (r.δ_map_of_gt j hgt)
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply,
      singular_const_apply] at hz
    exact hz
  have ha := hface 2 a r.δ_succ_succ_map
  have hb := hface 0 b r.δ_castSucc_castSucc_map
  have hc := hface 1 c r.δ_succ_castSucc_map
  have hf' : f.val = (F.comp ⟨stdSimplex.map (2 : Fin (n + 4)).succAbove,
      stdSimplex.continuous_map _⟩).comp q := by rw [ha]; exact hf
  have hg' : g.val = (F.comp ⟨stdSimplex.map (0 : Fin (n + 4)).succAbove,
      stdSimplex.continuous_map _⟩).comp q := by rw [hb]; exact hg
  have H := stdSimplex_central_face_homotopicRel_transAt (n + 1) q hq0 hqs F
    (TopCat.toSSetObj₀Equiv x) hF f g hf' hg'
  rw [hc, ← hh] at H
  have heq : (Quotient.mk _ h : HomotopyGroup (Fin (n + 2)) X (TopCat.toSSetObj₀Equiv x)) =
      Quotient.mk _ (GenLoop.transAt (0 : Fin (n + 2)) f g) := Quotient.sound H
  have hmul := HomotopyGroup.mul_spec (i := (0 : Fin (n + 2))) (p := g) (q := f)
  exact heq.trans (hmul.symm.trans
    (@mul_comm (HomotopyGroup (Fin (n + 2)) X (TopCat.toSSetObj₀Equiv x)) _ _ _))

end PoincareConjecture.Proofs.M02.Topology
