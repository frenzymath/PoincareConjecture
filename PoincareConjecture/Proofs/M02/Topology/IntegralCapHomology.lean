import PoincareConjecture.Proofs.M02.Topology.IntegralCapBoundary









set_option autoImplicit false

open CategoryTheory

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in
def integralCapOneHomology :
    (integralChains X).homology 3 →ₗ[Int]
      (integralCohomology X 1 →ₗ[Int] (integralChains X).homology 2) := by
  let C := integralChains X
  let S := C.sc' 4 3 2
  let T := (integralCochains X).sc' 0 1 2
  let U := C.sc' 3 2 1
  let Z := LinearMap.ker S.g.hom
  let W := LinearMap.ker T.g.hom
  let P := LinearMap.ker U.g.hom
  letI : Module Int Z := Z.module
  letI : Module Int W := W.module
  letI : Module Int P := P.module
  let B : Submodule Int Z := LinearMap.range S.moduleCatToCycles
  let D : Submodule Int W := LinearMap.range T.moduleCatToCycles
  let Q : Submodule Int P := LinearMap.range U.moduleCatToCycles
  letI : Module Int (Z ⧸ B) := Submodule.Quotient.module B
  letI : Module Int (W ⧸ D) := Submodule.Quotient.module D
  letI : Module Int (P ⧸ Q) := Submodule.Quotient.module Q
  letI : Module Int (W →ₗ[Int] P) := LinearMap.module
  letI : Module Int (W →ₗ[Int] (P ⧸ Q)) := LinearMap.module
  letI : Module Int (W ⧸ D →ₗ[Int] (P ⧸ Q)) := LinearMap.module
  have hcycle (z : Z) (phi : W) :
      C.d 2 1 (integralCap 2 1 z.val phi.val) = 0 := by
    have hz : C.d 3 2 z.val = 0 := z.property
    have hp : (integralCochains X).d 1 2 phi.val = 0 := phi.property
    rw [integralCap_three_one_boundary (X := X), hz, hp]
    simp only [map_zero, LinearMap.zero_apply, sub_self]
  let E0 : Z →ₗ[Int] (W →ₗ[Int] P) :=
    { toFun := fun z =>
        ((integralCap 2 1 z.val).comp (LinearMap.ker T.g.hom).subtype).codRestrict
          (LinearMap.ker U.g.hom) (fun phi => hcycle z phi)
      map_add' := by
        intro z w
        apply LinearMap.ext
        intro phi
        apply Subtype.ext
        exact congrArg (fun f : (integralCochains X).X 1 →ₗ[Int] C.X 2 => f phi.val)
          ((integralCap 2 1).map_add z.val w.val)
      map_smul' := by
        intro a z
        apply LinearMap.ext
        intro phi
        apply Subtype.ext
        change integralCap 2 1 (S.X₂.isModule.smul a z.val) phi.val =
          U.X₂.isModule.smul a (integralCap 2 1 z.val phi.val)
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
        exact integralCap_chain_smul 2 1 a z.val phi.val }
  let E : Z →ₗ[Int] (W →ₗ[Int] (P ⧸ Q)) :=
    (LinearMap.compRight Int Q.mkQ).comp E0
  have hD (z : Z) : D ≤ LinearMap.ker (E z) := by
    rintro _ ⟨psi, rfl⟩
    change Q.mkQ (E0 z (T.moduleCatToCycles psi)) = 0
    apply (Submodule.Quotient.mk_eq_zero Q).mpr
    refine ⟨-(integralCap 3 0 z.val psi), ?_⟩
    apply Subtype.ext
    change C.d 3 2 (-(integralCap 3 0 z.val psi)) =
      integralCap 2 1 z.val ((integralCochains X).d 0 1 psi)
    have hz : C.d 3 2 z.val = 0 := z.property
    rw [map_neg, integralCap_three_zero_boundary, hz]
    simp only [map_zero, LinearMap.zero_apply, zero_sub, neg_neg]
  let ED : Z →ₗ[Int] (W ⧸ D →ₗ[Int] (P ⧸ Q)) :=
    { toFun := fun z => D.liftQ (E z) (hD z)
      map_add' := by
        intro z w
        apply D.linearMap_qext
        apply LinearMap.ext
        intro phi
        exact congrArg (fun f : W →ₗ[Int] (P ⧸ Q) => f phi) (E.map_add z w)
      map_smul' := by
        intro a z
        apply D.linearMap_qext
        apply LinearMap.ext
        intro phi
        exact congrArg (fun f : W →ₗ[Int] (P ⧸ Q) => f phi) (E.map_smul a z) }
  have hB : B ≤ LinearMap.ker ED := by
    rintro _ ⟨c, rfl⟩
    apply D.linearMap_qext
    apply LinearMap.ext
    intro phi
    change Q.mkQ (E0 (S.moduleCatToCycles c) phi) = 0
    apply (Submodule.Quotient.mk_eq_zero Q).mpr
    refine ⟨-(integralCap 3 1 c phi.val), ?_⟩
    apply Subtype.ext
    change C.d 3 2 (-(integralCap 3 1 c phi.val)) =
      integralCap 2 1 (C.d 4 3 c) phi.val
    have hp : (integralCochains X).d 1 2 phi.val = 0 := phi.property
    rw [map_neg, integralCap_four_one_boundary, hp]
    simp only [map_zero, zero_sub, neg_neg]
    rfl
  let EQ : Z ⧸ B →ₗ[Int] (W ⧸ D →ₗ[Int] (P ⧸ Q)) := B.liftQ ED hB
  let eS := C.homologyIsoSc' 4 3 2 (by simp) (by simp)
  let eT := (integralCochains X).homologyIsoSc' 0 1 2 (by simp) (by simp)
  let eU := C.homologyIsoSc' 3 2 1 (by simp) (by simp)
  letI : Module Int ((integralCochains X).homology 1 →ₗ[Int] (P ⧸ Q)) := LinearMap.module
  let H := (EQ.compl₂ (eT ≪≫ T.moduleCatHomologyIso).toLinearEquiv.toLinearMap).comp
    (eS ≪≫ S.moduleCatHomologyIso).toLinearEquiv.toLinearMap
  let e : (P ⧸ Q) →ₗ[Int] C.homology 2 :=
    (U.moduleCatHomologyIso.symm ≪≫ eU.symm).toLinearEquiv.toLinearMap
  exact
    { toFun := fun z => e.comp (H z)
      map_add' := by
        intro z w
        apply LinearMap.ext
        intro phi
        change e (H (z + w) phi) = e (H z phi) + e (H w phi)
        rw [H.map_add, LinearMap.add_apply, e.map_add]
      map_smul' := by
        intro a z
        apply LinearMap.ext
        intro phi
        change e (H (((integralChains X).homology 3).isModule.smul a z) phi) =
          a • e (H z phi)
        rw [int_smul_eq_zsmul]
        let ev : ((integralCochains X).homology 1 →ₗ[Int] (P ⧸ Q)) →+ (P ⧸ Q) :=
          { toFun := fun f => f phi
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        exact (congrArg (fun f : (integralCochains X).homology 1 →ₗ[Int] (P ⧸ Q) =>
          e (ev f)) (map_zsmul H.toAddMonoidHom a z)).trans
            ((congrArg e (map_zsmul ev a (H z))).trans
              (map_zsmul e.toAddMonoidHom a (ev (H z)))) }

end

end PoincareConjecture.Proofs.M02.Topology
