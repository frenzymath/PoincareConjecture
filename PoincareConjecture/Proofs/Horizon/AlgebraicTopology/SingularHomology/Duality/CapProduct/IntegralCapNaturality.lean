import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralRelativeCap







set_option autoImplicit false

open CategoryTheory Limits
open scoped BigOperators

universe u

namespace Poincare.Topology

noncomputable section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem generator_map_apply (n : Nat) (f : C(X, Y))
    (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
    (integralChainsFunctor.map (TopCat.ofHom f)).f n (integralSingularGenerator s a) =
      integralSingularGenerator (f.comp s) a :=
  congrArg (fun k => k a) (integralSingularGenerator_map s f)

private theorem integralHom_smul {A B : ModuleCat.{u} Int} (f : A ⟶ B)
    (a : Int) (z : A) : f (a • z) = a • f z :=
  map_zsmul f.hom.toAddMonoidHom a z

theorem integralCap_naturality (f : C(X, Y)) (p q : Nat)
    (c : (integralChains X).X (p + q)) (phi : (integralCochains Y).X q) :
    (integralChainsFunctor.map (TopCat.ofHom f)).f p
      (integralCap p q c ((integralDualMap
        (integralChainsFunctor.map (TopCat.ofHom f))).f q phi)) =
    integralCap p q ((integralChainsFunctor.map (TopCat.ofHom f)).f (p + q) c) phi := by
  classical
  rw [integral_chain_finite_representation (p + q) c]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  let a := integralChainCoordinates X (p + q) c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : integralSingularGenerator s a =
      a.down • integralSingularGenerator s (ULift.up 1) := by
    conv_lhs => rw [ha, integralHom_smul]
  change (integralChainsFunctor.map (TopCat.ofHom f)).f p
    (integralCap p q (integralSingularGenerator s a) _) =
      integralCap p q ((integralChainsFunctor.map (TopCat.ofHom f)).f (p + q)
        (integralSingularGenerator s a)) phi
  rw [hg, integralCap_chain_smul, integralHom_smul, integralHom_smul,
    integralCap_chain_smul, generator_map_apply, integralCap_generator,
    integralCap_generator, integralHom_smul, generator_map_apply]
  congr 1
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc]
  congr 1
  change ((show (integralChains Y).X q ⟶ integralCoefficient from phi)
      ((integralChainsFunctor.map (TopCat.ofHom f)).f q
        (integralSingularGenerator (s.comp (integralFrontFace p q)) (ULift.up 1)))).down = _
  rw [generator_map_apply]

theorem integralRelativeCap_naturality (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (p q : Nat)
    (c : (integralRelativeChains A).X (p + q)) (phi : (integralCochains Y).X q) :
    (integralRelativeMap f hf).f p
      (integralRelativeCap A p q c ((integralDualMap
        (integralChainsFunctor.map (TopCat.ofHom f))).f q phi)) =
    integralRelativeCap B p q ((integralRelativeMap f hf).f (p + q) c) phi := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f (p + q))).mp inferInstance c
  have hpi (n : Nat) (z : (integralChains X).X n) :
      (integralRelativeMap f hf).f n ((integralRelativeProjection A).f n z) =
      (integralRelativeProjection B).f n
        ((integralChainsFunctor.map (TopCat.ofHom f)).f n z) :=
    congrArg (fun k => k.f n z) (integralRelativeMap_projection f hf)
  rw [integralRelativeCap_projection, hpi, hpi, integralRelativeCap_projection,
    integralCap_naturality]

end

end Poincare.Topology
