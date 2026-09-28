import PoincareConjecture.Proofs.M02.SimplexCompression
import PoincareConjecture.Proofs.M02.HurewiczMap
import PoincareConjecture.Proofs.M02.Topology.SingularHomologyDetection

set_option autoImplicit false

open CategoryTheory Simplicial
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M02

theorem homotopyGroupSingularHomologyMap_injective
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X) (n : Nat)
    (hpi : forall k : Nat, 1 <= k -> k <= n + 1 ->
      Subsingleton (HomotopyGroup.Pi k X x)) :
    Function.Injective
      (homotopyGroupSingularHomologyMap
        (ModuleCat.of Int (ULift.{u} Int)) X (n + 1) x) := by
  classical
  let Y := TopCat.toSSet.obj X
  let R := ModuleCat.of Int (ULift.{u} Int)
  let C := Y.chainComplex R
  let x0 : Y.obj (Opposite.op (SimplexCategory.mk 0)) := TopCat.toSSetObj₀Equiv.symm x
  have hx0 : TopCat.toSSetObj₀Equiv x0 = x := TopCat.toSSetObj₀Equiv.apply_symm_apply x
  have hconstant (d : Nat) :
      SSet.yonedaEquiv (SSet.const x0 :
        (SSet.stdSimplex.{u}.obj (SimplexCategory.mk d)) ⟶ Y) =
        singularConstantSimplex X d x := by
    apply (X.toSSetObjEquiv _).injective
    ext z
    rw [singular_const_apply]
    simpa only [singularConstantSimplex, Equiv.apply_symm_apply,
      ContinuousMap.const_apply] using hx0
  obtain ⟨K, r, H, _hcoh, _hconst, hface, htrace, hfix⟩ :=
    exists_normalized_singularSimplex_straightening X x (n + 1) hpi
  have pointed (s : Y.obj (Opposite.op (SimplexCategory.mk (n + 2)))) :
      Exists fun a : Y.PtSimplex (n + 2) x0 =>
        a.map = SSet.yonedaEquiv.symm (r s) := by
    apply exists_pointedSimplex_of_constant_faces Y (n + 1) x0
    intro j
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, hface, hconstant]
  choose rho hrhoMap using pointed
  have hrhoSimplex (s : Y.obj (Opposite.op (SimplexCategory.mk (n + 2)))) :
      SSet.yonedaEquiv (rho s).map = r s := by
    rw [hrhoMap, Equiv.apply_symm_apply]
  have hpointedFace (a : Y.PtSimplex (n + 2) x0) (j : Fin (n + 3)) :
      Y.δ j (SSet.yonedaEquiv a.map) = singularConstantSimplex X (n + 1) x := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.PtSimplex.δ_map, hconstant]
  have hrho (a : Y.PtSimplex (n + 2) x0) : rho (SSet.yonedaEquiv a.map) = a := by
    apply SSet.RelativeMorphism.ext
    apply SSet.yonedaEquiv.injective
    rw [hrhoSimplex, (hfix _ (hpointedFace a)).1]
  have hfill (s : Y.obj (Opposite.op (SimplexCategory.mk (n + 3)))) :
      Exists fun F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶ Y =>
        forall j : Fin (n + 4), SSet.stdSimplex.δ j ≫ F = (rho (Y.δ j s)).map := by
    obtain ⟨s', _F, hs', _hF⟩ := exists_singularSimplex_straightening_extension
      X (n + 1) r H (fun t => (K (n + 1) le_rfl t).toContinuousMap) htrace s
    refine ⟨SSet.yonedaEquiv.symm s', ?_⟩
    intro j
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, hs', hrhoSimplex]
  let cycle (p : GenLoop (Fin (n + 2)) X x) : R ⟶ C.cycles (n + 2) :=
    C.liftCycles (Y.ιChainComplex (genLoopSingularSimplex X p) -
      Y.ιChainComplex (singularConstantSimplex X (n + 2) x)) (n + 1) (by simp)
      (simplicialSimplexDifference_d_eq_zero R Y (genLoopSingularSimplex X p)
        (singularConstantSimplex X (n + 2) x)
        (fun j => (genLoopSingularSimplex_face X p j).trans
          (singularConstantSimplex_face X x j).symm))
  have hcycle (p : GenLoop (Fin (n + 2)) X x) :
      cycle p ≫ C.iCycles (n + 2) = Y.ιChainComplex (genLoopSingularSimplex X p) -
        Y.ιChainComplex (singularConstantSimplex X (n + 2) x) := by
    simp only [cycle, HomologicalComplex.liftCycles_i]
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro p q hpq
  change cycle p ≫ C.homologyπ (n + 2) = cycle q ≫ C.homologyπ (n + 2) at hpq
  let a := rho (genLoopSingularSimplex X p)
  let b := rho (genLoopSingularSimplex X q)
  have ha : SSet.yonedaEquiv a.map = genLoopSingularSimplex X p :=
    (hrhoSimplex _).trans ((hfix _ (genLoopSingularSimplex_face X p)).1)
  have hb : SSet.yonedaEquiv b.map = genLoopSingularSimplex X q :=
    (hrhoSimplex _).trans ((hfix _ (genLoopSingularSimplex_face X q)).1)
  have hclasses := singularPointedSimplexClass_eq_of_homology_eq X n x0 rho hrho hfill
    a b (cycle p) (cycle q)
    (by rw [ha, hconstant]; exact hcycle p)
    (by rw [hb, hconstant]; exact hcycle q) hpq
  have Hcube : GenLoop.Homotopic
      (singularPointedSimplexGenLoop X (n + 1) x0 a)
      (singularPointedSimplexGenLoop X (n + 1) x0 b) := Quotient.exact hclasses
  change ContinuousMap.HomotopicRel
    (singularPointedSimplexGenLoop X (n + 1) x0 a).val
    (singularPointedSimplexGenLoop X (n + 1) x0 b).val (Cube.boundary (Fin (n + 2))) at Hcube
  rw [singularPointedSimplexGenLoop_val, singularPointedSimplexGenLoop_val] at Hcube
  have Hsimplex := (stdSimplex_cube_coordinates_homotopicRel_iff (n + 2)
    (stdSimplexCubeMap (n + 2)) (stdSimplexCubeMap_spec (n + 2)).1
    (stdSimplexCubeMap_spec (n + 2)).2
    (X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map))
    (X.toSSetObjEquiv _ (SSet.yonedaEquiv b.map))).mp Hcube
  rw [ha, hb] at Hsimplex
  obtain ⟨J⟩ := Hsimplex
  let e := Classical.choose (exists_stdSimplex_cube_pair_homeomorph (n + 2))
  let eC : C((Fin (n + 2) -> unitInterval), stdSimplex Real (Fin (n + 3))) :=
    ⟨e.symm, e.symm.continuous⟩
  have hpval : (X.toSSetObjEquiv _ (genLoopSingularSimplex X p)).comp eC = p.val := by
    simp only [genLoopSingularSimplex, Equiv.apply_symm_apply]
    ext t
    exact congrArg p (e.apply_symm_apply t)
  have hqval : (X.toSSetObjEquiv _ (genLoopSingularSimplex X q)).comp eC = q.val := by
    simp only [genLoopSingularSimplex, Equiv.apply_symm_apply]
    ext t
    exact congrArg q (e.apply_symm_apply t)
  apply Quotient.sound
  refine ⟨{ toHomotopy := (J.toHomotopy.compContinuousMap eC).cast hpval hqval
            prop' := ?_ }⟩
  intro time t ht
  have hboundary : Exists fun i : Fin (n + 3) => e.symm t i = 0 := by
    apply (Classical.choose_spec (exists_stdSimplex_cube_pair_homeomorph (n + 2))
      (e.symm t)).mpr
    change e (e.symm t) ∈ Cube.boundary (Fin (n + 2))
    simpa only [e.apply_symm_apply] using ht
  change J (time, e.symm t) = p t
  exact (J.eq_fst time hboundary).trans (DFunLike.congr_fun hpval t)

end PoincareConjecture.Proofs.M02
