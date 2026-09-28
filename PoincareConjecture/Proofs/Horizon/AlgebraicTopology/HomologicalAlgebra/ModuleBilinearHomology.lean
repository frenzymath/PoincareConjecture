import Mathlib.Algebra.Homology.ShortComplex.ModuleCat









set_option autoImplicit false

open CategoryTheory

universe u

namespace Poincare.Topology

noncomputable section

attribute [local instance 2000] Submodule.Quotient.module
attribute [local instance 2000] Submodule.module

abbrev moduleHomologyClass (S : ShortComplex (ModuleCat.{u} Int))
    (z : LinearMap.ker S.g.hom) : S.homology :=
  S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)

theorem moduleHomologyClass_surjective (S : ShortComplex (ModuleCat.{u} Int)) :
    Function.Surjective (moduleHomologyClass S) := by
  intro a
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective S.moduleCatLeftHomologyData.π).mp
    inferInstance (S.moduleCatHomologyIso.hom a)
  refine ⟨z, ?_⟩
  dsimp only [moduleHomologyClass]
  rw [hz]
  exact S.moduleCatHomologyIso.hom_inv_id_apply a

set_option backward.isDefEq.respectTransparency false in
private def moduleBilinearHomologyData
    (S T U : ShortComplex (ModuleCat.{u} Int))
    (F : S.X₂ →ₗ[Int] (T.X₂ →ₗ[Int] U.X₂))
    (hcycle : ∀ z : LinearMap.ker S.g.hom, ∀ w : LinearMap.ker T.g.hom,
      U.g (F z.val w.val) = 0)
    (hleft : ∀ a : S.X₁, ∀ w : LinearMap.ker T.g.hom,
      F (S.f a) w.val ∈ LinearMap.range U.f.hom)
    (hright : ∀ z : LinearMap.ker S.g.hom, ∀ b : T.X₁,
      F z.val (T.f b) ∈ LinearMap.range U.f.hom) :
    { G : S.homology →ₗ[Int] (T.homology →ₗ[Int] U.homology) //
      ∀ z : LinearMap.ker S.g.hom, ∀ w : LinearMap.ker T.g.hom,
        G (moduleHomologyClass S z) (moduleHomologyClass T w) =
          moduleHomologyClass U ⟨F z.val w.val, hcycle z w⟩ } := by
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
  let E0 : Z →ₗ[Int] (W →ₗ[Int] P) :=
    { toFun := fun z => ((F z.val).comp W.subtype).codRestrict P (hcycle z)
      map_add' := by
        intro z w
        apply LinearMap.ext
        intro phi
        apply Subtype.ext
        exact congrArg (fun f : T.X₂ →ₗ[Int] U.X₂ => f phi.val) (F.map_add z.val w.val)
      map_smul' := by
        intro a z
        apply LinearMap.ext
        intro phi
        apply Subtype.ext
        change F (S.X₂.isModule.smul a z.val) phi.val =
          U.X₂.isModule.smul a (F z.val phi.val)
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
        exact congrArg (fun f : T.X₂ →ₗ[Int] U.X₂ => f phi.val)
          (map_zsmul F.toAddMonoidHom a z.val) }
  let E : Z →ₗ[Int] (W →ₗ[Int] (P ⧸ Q)) :=
    (LinearMap.compRight Int Q.mkQ).comp E0
  have hD (z : Z) : D ≤ LinearMap.ker (E z) := by
    rintro _ ⟨b, rfl⟩
    change Q.mkQ (E0 z (T.moduleCatToCycles b)) = 0
    apply (Submodule.Quotient.mk_eq_zero Q).mpr
    obtain ⟨a, ha⟩ := hright z b
    exact ⟨a, Subtype.ext ha⟩
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
    rintro _ ⟨a, rfl⟩
    apply D.linearMap_qext
    apply LinearMap.ext
    intro phi
    change Q.mkQ (E0 (S.moduleCatToCycles a) phi) = 0
    apply (Submodule.Quotient.mk_eq_zero Q).mpr
    obtain ⟨b, hb⟩ := hleft a phi
    exact ⟨b, Subtype.ext hb⟩
  let EQ : Z ⧸ B →ₗ[Int] (W ⧸ D →ₗ[Int] (P ⧸ Q)) := B.liftQ ED hB
  letI : Module Int (T.homology →ₗ[Int] (P ⧸ Q)) := LinearMap.module
  let H := (EQ.compl₂ T.moduleCatHomologyIso.toLinearEquiv.toLinearMap).comp
    S.moduleCatHomologyIso.toLinearEquiv.toLinearMap
  let e : (P ⧸ Q) →ₗ[Int] U.homology := U.moduleCatHomologyIso.symm.toLinearEquiv.toLinearMap
  let G : S.homology →ₗ[Int] (T.homology →ₗ[Int] U.homology) :=
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
        change e (H (S.homology.isModule.smul a z) phi) = a • e (H z phi)
        rw [int_smul_eq_zsmul]
        let ev : (T.homology →ₗ[Int] (P ⧸ Q)) →+ (P ⧸ Q) :=
          { toFun := fun f => f phi
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        exact (congrArg (fun f : T.homology →ₗ[Int] (P ⧸ Q) => e (ev f))
          (map_zsmul H.toAddMonoidHom a z)).trans
            ((congrArg e (map_zsmul ev a (H z))).trans
              (map_zsmul e.toAddMonoidHom a (ev (H z)))) }
  refine ⟨G, ?_⟩
  intro z w
  change e (EQ (S.moduleCatHomologyIso.hom (moduleHomologyClass S z))
    (T.moduleCatHomologyIso.hom (moduleHomologyClass T w))) = _
  have hs : S.moduleCatHomologyIso.hom (moduleHomologyClass S z) = B.mkQ z :=
    S.moduleCatHomologyIso.inv_hom_id_apply _
  have ht : T.moduleCatHomologyIso.hom (moduleHomologyClass T w) = D.mkQ w :=
    T.moduleCatHomologyIso.inv_hom_id_apply _
  rw [hs, ht]
  rfl

def moduleBilinearHomology
    (S T U : ShortComplex (ModuleCat.{u} Int))
    (F : S.X₂ →ₗ[Int] (T.X₂ →ₗ[Int] U.X₂))
    (hcycle : ∀ z : LinearMap.ker S.g.hom, ∀ w : LinearMap.ker T.g.hom,
      U.g (F z.val w.val) = 0)
    (hleft : ∀ a : S.X₁, ∀ w : LinearMap.ker T.g.hom,
      F (S.f a) w.val ∈ LinearMap.range U.f.hom)
    (hright : ∀ z : LinearMap.ker S.g.hom, ∀ b : T.X₁,
      F z.val (T.f b) ∈ LinearMap.range U.f.hom) :
    S.homology →ₗ[Int] (T.homology →ₗ[Int] U.homology) :=
  (moduleBilinearHomologyData S T U F hcycle hleft hright).val

theorem moduleBilinearHomology_class
    (S T U : ShortComplex (ModuleCat.{u} Int))
    (F : S.X₂ →ₗ[Int] (T.X₂ →ₗ[Int] U.X₂))
    (hcycle : ∀ z : LinearMap.ker S.g.hom, ∀ w : LinearMap.ker T.g.hom,
      U.g (F z.val w.val) = 0)
    (hleft : ∀ a : S.X₁, ∀ w : LinearMap.ker T.g.hom,
      F (S.f a) w.val ∈ LinearMap.range U.f.hom)
    (hright : ∀ z : LinearMap.ker S.g.hom, ∀ b : T.X₁,
      F z.val (T.f b) ∈ LinearMap.range U.f.hom)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom) :
    moduleBilinearHomology S T U F hcycle hleft hright
      (moduleHomologyClass S z) (moduleHomologyClass T w) =
    moduleHomologyClass U ⟨F z.val w.val, hcycle z w⟩ :=
  (moduleBilinearHomologyData S T U F hcycle hleft hright).property z w

end

end Poincare.Topology
