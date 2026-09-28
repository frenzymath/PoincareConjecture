import PoincareConjecture.Proofs.M02.Topology.IntegralCapNaturality

set_option autoImplicit false

open CategoryTheory Limits
open scoped BigOperators

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X]

theorem integralCap_relative_cochain_zero (A : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ LinearMap.range ((integralSubspaceChains A).f (p + q)).hom)
    (phi : (integralRelativeCochains A).X q) :
    integralCap p q c ((integralDualMap (integralRelativeProjection A)).f q phi) = 0 := by
  classical
  have hsupport := (integral_subspace_range_iff A (p + q) c).mp hc
  rw [integral_chain_finite_representation (p + q) c]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro s hs
  let a := integralChainCoordinates X (p + q) c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : integralSingularGenerator s a =
      a.down • integralSingularGenerator s (ULift.up 1) := by
    conv_lhs => rw [ha, map_zsmul]
  change integralCap p q (integralSingularGenerator s a) _ = 0
  rw [hg, integralCap_chain_smul, integralCap_generator]
  have hsA : Set.range (s.comp (integralFrontFace p q)) ⊆ A := by
    rintro _ ⟨z, rfl⟩
    exact hsupport s hs ⟨integralFrontFace p q z, rfl⟩
  obtain ⟨b, hb⟩ := integralSingularGenerator_mem_subspace A
    (s.comp (integralFrontFace p q)) hsA (ULift.up 1)
  have hzero : (integralRelativeProjection A).f q
      (integralSingularGenerator (s.comp (integralFrontFace p q)) (ULift.up 1)) = 0 := by
    rw [← hb]
    exact congrArg (fun f => f.f q b) (cokernel.condition (integralSubspaceChains A))
  change a.down • (((show (integralRelativeChains A).X q ⟶ integralCoefficient from phi)
    ((integralRelativeProjection A).f q
      (integralSingularGenerator (s.comp (integralFrontFace p q)) (ULift.up 1)))).down •
        integralSingularGenerator (s.comp (integralBackFace p q)) (ULift.up 1)) = 0
  rw [hzero, map_zero]
  simp only [ULift.zero_down, zero_smul]
  exact zsmul_zero _

private def supportCapRaw (A : Set X) (p q : Nat) :
    (integralChains X).X (p + q) →ₗ[Int]
      ((integralRelativeCochains A).X q →ₗ[Int] (integralChains X).X p) := by
  let pull := ((integralDualMap (integralRelativeProjection A)).f q).hom
  exact
    { toFun := fun c => (integralCap p q c).comp pull
      map_add' := by
        intro c d
        apply LinearMap.ext
        intro phi
        exact congrArg (fun f : (integralCochains X).X q →ₗ[Int]
          (integralChains X).X p => f (pull phi)) ((integralCap p q).map_add c d)
      map_smul' := by
        intro a c
        apply LinearMap.ext
        intro phi
        change integralCap p q (((integralChains X).X (p + q)).isModule.smul a c)
          (pull phi) = a • integralCap p q c (pull phi)
        rw [int_smul_eq_zsmul]
        exact integralCap_chain_smul p q a c (pull phi) }

def integralSupportCap (A : Set X) (p q : Nat) :
    (integralRelativeChains A).X (p + q) →ₗ[Int]
      ((integralRelativeCochains A).X q →ₗ[Int] (integralChains X).X p) := by
  let W := ModuleCat.of Int ((integralRelativeCochains A).X q →ₗ[Int] (integralChains X).X p)
  let F : (integralChains X).X (p + q) ⟶ W := ModuleCat.ofHom (supportCapRaw A p q)
  let S := (integralPairSequence A).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) (p + q))
  letI : Epi S.g := ((integralPairSequence_shortExact A).map_of_exact _).epi_g
  have hS : S.Exact := (integralPairSequence_shortExact A).exact.map _
  have hzero : S.f ≫ F = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro phi
    exact integralCap_relative_cochain_zero A p q _ ⟨c, rfl⟩ phi
  exact (hS.desc F hzero).hom

theorem integralSupportCap_projection (A : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q)) (phi : (integralRelativeCochains A).X q) :
    integralSupportCap A p q ((integralRelativeProjection A).f (p + q) c) phi =
      integralCap p q c ((integralDualMap (integralRelativeProjection A)).f q phi) := by
  let : Epi (((integralPairSequence A).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) (p + q))).g) :=
      ((integralPairSequence_shortExact A).map_of_exact _).epi_g
  unfold integralSupportCap
  have h := ShortComplex.Exact.g_desc
    ((integralPairSequence_shortExact A).exact.map
      (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) (p + q)))
    (ModuleCat.ofHom (supportCapRaw A p q))
  have hz : ((integralSubspaceChains A).f (p + q)) ≫
      ModuleCat.ofHom (supportCapRaw A p q) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro psi
    exact integralCap_relative_cochain_zero A p q _ ⟨b, rfl⟩ psi
  exact congrArg (fun f => f c phi) (h hz)

theorem integralSupportCap_naturality {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (p q : Nat)
    (c : (integralRelativeChains A).X (p + q)) (phi : (integralRelativeCochains B).X q) :
    (integralChainsFunctor.map (TopCat.ofHom f)).f p
      (integralSupportCap A p q c ((integralDualMap (integralRelativeMap f hf)).f q phi)) =
    integralSupportCap B p q ((integralRelativeMap f hf).f (p + q) c) phi := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f (p + q))).mp inferInstance c
  have hpi (n : Nat) (z : (integralChains X).X n) :
      (integralRelativeMap f hf).f n ((integralRelativeProjection A).f n z) =
      (integralRelativeProjection B).f n
        ((integralChainsFunctor.map (TopCat.ofHom f)).f n z) :=
    congrArg (fun k => k.f n z) (integralRelativeMap_projection f hf)
  have hco : (integralDualMap (integralRelativeProjection A)).f q
        ((integralDualMap (integralRelativeMap f hf)).f q phi) =
      (integralDualMap (integralChainsFunctor.map (TopCat.ofHom f))).f q
        ((integralDualMap (integralRelativeProjection B)).f q phi) := by
    change (integralRelativeProjection A).f q ≫ (integralRelativeMap f hf).f q ≫
      (show (integralRelativeChains B).X q ⟶ integralCoefficient from phi) =
        (integralChainsFunctor.map (TopCat.ofHom f)).f q ≫
          (integralRelativeProjection B).f q ≫
            (show (integralRelativeChains B).X q ⟶ integralCoefficient from phi)
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k.f q ≫
      (show (integralRelativeChains B).X q ⟶ integralCoefficient from phi))
        (integralRelativeMap_projection f hf)
  rw [integralSupportCap_projection, hpi, integralSupportCap_projection, hco,
    integralCap_naturality]

end

end PoincareConjecture.Proofs.M02.Topology
