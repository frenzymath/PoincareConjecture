import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubeSimplexDescent
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Simplex.Singular.SimplexFaceHomotopy
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.SingularComplex.PointedHorn

set_option autoImplicit false

open CategoryTheory Simplicial

universe u

namespace Poincare.Topology

theorem exists_singular_pointedSimplex_of_genLoop (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (q : C((Fin (n + 1) -> unitInterval), stdSimplex Real (Fin (n + 2))))
    (hq0 : forall t, q t 0 = ∏ k : Fin (n + 1), (1 - (t k : Real)))
    (hqs : forall t (j : Fin (n + 1)), q t j.succ =
      (t j : Real) * ∏ k : Fin (n + 1), if j < k then 1 - (t k : Real) else 1)
    (f : GenLoop (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x)) :
    Exists fun a : (TopCat.toSSet.obj X).PtSimplex (n + 1) x =>
      (X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map)).comp q = f.val := by
  obtain ⟨F, hF, hboundary⟩ := exists_stdSimplex_map_of_cube_boundary (n + 1) q hq0 hqs
    f.val (TopCat.toSSetObj₀Equiv x) f.property
  let G : (Δ[n + 1] : SSet.{u}) ⟶ TopCat.toSSet.obj X :=
    SSet.yonedaEquiv.symm ((X.toSSetObjEquiv _).symm F)
  have hG : X.toSSetObjEquiv _ (SSet.yonedaEquiv G) = F := by
    dsimp only [G]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hface (j : Fin (n + 2)) : SSet.stdSimplex.δ j ≫ G = SSet.const x := by
    apply SSet.yonedaEquiv.injective
    apply (X.toSSetObjEquiv _).injective
    ext z
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply,
      hG, singular_const_apply]
    exact hboundary _ ⟨j, stdSimplex_face_zero n j z⟩
  obtain ⟨a, ha⟩ := exists_pointedSimplex_of_constant_faces (TopCat.toSSet.obj X) n x G hface
  refine ⟨a, ?_⟩
  rw [ha, hG]
  exact hF

end Poincare.Topology
