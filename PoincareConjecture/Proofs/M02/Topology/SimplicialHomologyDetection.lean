import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Span.Basic








set_option autoImplicit false

open CategoryTheory Limits Simplicial

universe u

namespace PoincareConjecture.Proofs.M02.Topology


theorem simplicial_values_eq_of_homology_eq
    (X : SSet.{u}) (n : Nat) (A : Type u) [AddCommGroup A]
    (v : X.obj (Opposite.op (SimplexCategory.mk (n + 1))) -> A)
    (hv : forall f : X.obj (Opposite.op (SimplexCategory.mk (n + 2))),
      (∑ j : Fin (n + 3), ((-1 : Int) ^ j.val) • v (X.δ j f)) = 0)
    (s t c : X.obj (Opposite.op (SimplexCategory.mk (n + 1))))
    (z w : ModuleCat.of Int (ULift.{u} Int) ⟶
      (X.chainComplex (ModuleCat.of Int (ULift.{u} Int))).cycles (n + 1))
    (hz : z ≫ (X.chainComplex (ModuleCat.of Int (ULift.{u} Int))).iCycles (n + 1) =
      X.ιChainComplex s - X.ιChainComplex c)
    (hw : w ≫ (X.chainComplex (ModuleCat.of Int (ULift.{u} Int))).iCycles (n + 1) =
      X.ιChainComplex t - X.ιChainComplex c)
    (heq : z ≫ (X.chainComplex (ModuleCat.of Int (ULift.{u} Int))).homologyπ (n + 1) =
      w ≫ (X.chainComplex (ModuleCat.of Int (ULift.{u} Int))).homologyπ (n + 1)) :
    v s = v t := by
  let R := ModuleCat.of Int (ULift.{u} Int)
  let G := ModuleCat.of Int A
  let K := X.chainComplex R
  let l (a : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) : R ⟶ G :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton Int A (v a)).comp
      (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap)
  have hl (a : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) (q : ULift.{u} Int) :
      (l a).hom q = q.down • v a := rfl
  let D : K.X (n + 1) ⟶ G := Sigma.desc l
  have hD (a : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
      X.ιChainComplex a ≫ D = l a := Sigma.ι_desc _ _
  have hd : K.d (n + 2) (n + 1) ≫ D = 0 := by
    apply SSet.chainComplex_hom_ext
    intro f
    rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, hD, comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_zero,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, hl]
    calc
      (∑ j : Fin (n + 3), ((-1 : Int) ^ j.val) • (q.down • v (X.δ j f))) =
          ∑ j : Fin (n + 3), q.down • (((-1 : Int) ^ j.val) • v (X.δ j f)) :=
        Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
      _ = q.down • (∑ j : Fin (n + 3), ((-1 : Int) ^ j.val) • v (X.δ j f)) :=
        Finset.smul_sum.symm
      _ = 0 := by rw [hv, smul_zero]
  have hk : K.toCycles (n + 2) (n + 1) ≫ (K.iCycles (n + 1) ≫ D) = 0 := by
    rw [← Category.assoc, HomologicalComplex.toCycles_i]
    exact hd
  let hcok := K.homologyIsCokernel (n + 2) (n + 1) (by simp)
  let E : K.homology (n + 1) ⟶ G :=
    hcok.desc (CokernelCofork.ofπ (K.iCycles (n + 1) ≫ D) hk)
  have hE : K.homologyπ (n + 1) ≫ E = K.iCycles (n + 1) ≫ D :=
    Cofork.IsColimit.π_desc hcok
  have hzE : (z ≫ K.homologyπ (n + 1)) ≫ E =
      (X.ιChainComplex s - X.ιChainComplex c) ≫ D := by
    rw [Category.assoc, hE, ← Category.assoc, hz]
  have hwE : (w ≫ K.homologyπ (n + 1)) ≫ E =
      (X.ιChainComplex t - X.ιChainComplex c) ≫ D := by
    rw [Category.assoc, hE, ← Category.assoc, hw]
  have hvalues := hzE.symm.trans
    ((congrArg (fun f : R ⟶ K.homology (n + 1) => f ≫ E) heq).trans hwE)
  rw [Preadditive.sub_comp, Preadditive.sub_comp, hD, hD, hD] at hvalues
  have hdiff : v s - v c = v t - v c := by
    simpa only [ModuleCat.hom_sub, LinearMap.sub_apply, hl, one_smul] using
      congrArg (fun f : R ⟶ G => f.hom (ULift.up 1)) hvalues
  exact sub_left_inj.mp hdiff

end PoincareConjecture.Proofs.M02.Topology
