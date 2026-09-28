import PoincareConjecture.Proofs.M02.Topology.IntegralCapBoundary
import PoincareConjecture.Proofs.M02.Topology.IntegralChainSupport

set_option autoImplicit false

open CategoryTheory Limits
open scoped BigOperators

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X]

theorem integralCap_mem_subspace (A : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ LinearMap.range ((integralSubspaceChains A).f (p + q)).hom)
    (phi : (integralCochains X).X q) :
    integralCap p q c phi ∈ LinearMap.range ((integralSubspaceChains A).f p).hom := by
  classical
  have hsupport := (integral_subspace_range_iff A (p + q) c).mp hc
  rw [integral_chain_finite_representation (p + q) c]
  simp only [map_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro s hs
  let a := integralChainCoordinates X (p + q) c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : integralSingularGenerator s a =
      a.down • integralSingularGenerator s (ULift.up 1) := by
    conv_lhs => rw [ha, map_zsmul]
  change integralCap p q (integralSingularGenerator s a) phi ∈ _
  rw [hg, integralCap_chain_smul]
  apply AddSubgroup.zsmul_mem (LinearMap.range
    ((integralSubspaceChains A).f p).hom).toAddSubgroup
  rw [integralCap_generator]
  apply AddSubgroup.zsmul_mem (LinearMap.range
    ((integralSubspaceChains A).f p).hom).toAddSubgroup
  apply integralSingularGenerator_mem_subspace
  rintro _ ⟨z, rfl⟩
  exact hsupport s hs ⟨integralBackFace p q z, rfl⟩

private def capRelativeRaw (A : Set X) (p q : Nat) :
    (integralChains X).X (p + q) →ₗ[Int]
      ((integralCochains X).X q →ₗ[Int] (integralRelativeChains A).X p) := by
  let pi := ((integralRelativeProjection A).f p).hom
  exact
    { toFun := fun c => pi.comp (integralCap p q c)
      map_add' := by
        intro c d
        apply LinearMap.ext
        intro phi
        change pi (integralCap p q (c + d) phi) =
          pi (integralCap p q c phi) + pi (integralCap p q d phi)
        rw [(integralCap p q).map_add, LinearMap.add_apply, pi.map_add]
      map_smul' := by
        intro a c
        apply LinearMap.ext
        intro phi
        change pi (((integralCap p q)
          (((integralChains X).X (p + q)).isModule.smul a c)) phi) =
          a • pi ((integralCap p q c) phi)
        rw [int_smul_eq_zsmul, integralCap_chain_smul]
        exact map_zsmul pi.toAddMonoidHom a _ }

private theorem capRelativeRaw_zero (A : Set X) (p q : Nat)
    (c : (integralChains A).X (p + q)) :
    capRelativeRaw A p q ((integralSubspaceChains A).f (p + q) c) = 0 := by
  apply LinearMap.ext
  intro phi
  change (integralRelativeProjection A).f p
    (integralCap p q ((integralSubspaceChains A).f (p + q) c) phi) = 0
  obtain ⟨b, hb⟩ := integralCap_mem_subspace A p q _ ⟨c, rfl⟩ phi
  rw [← hb]
  exact congrArg (fun f => f.f p b) (cokernel.condition (integralSubspaceChains A))

def integralRelativeCap (A : Set X) (p q : Nat) :
    (integralRelativeChains A).X (p + q) →ₗ[Int]
      ((integralCochains X).X q →ₗ[Int] (integralRelativeChains A).X p) := by
  let W := ModuleCat.of Int ((integralCochains X).X q →ₗ[Int] (integralRelativeChains A).X p)
  let F : (integralChains X).X (p + q) ⟶ W := ModuleCat.ofHom (capRelativeRaw A p q)
  let S := (integralPairSequence A).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) (p + q))
  letI : Epi S.g := ((integralPairSequence_shortExact A).map_of_exact _).epi_g
  have hS : S.Exact := (integralPairSequence_shortExact A).exact.map _
  have hzero : S.f ≫ F = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact capRelativeRaw_zero A p q c
  exact (hS.desc F hzero).hom

theorem integralRelativeCap_projection (A : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q)) (phi : (integralCochains X).X q) :
    integralRelativeCap A p q ((integralRelativeProjection A).f (p + q) c) phi =
      (integralRelativeProjection A).f p (integralCap p q c phi) := by
  let : Epi (((integralPairSequence A).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) (p + q))).g) :=
      ((integralPairSequence_shortExact A).map_of_exact _).epi_g
  unfold integralRelativeCap
  have h := ShortComplex.Exact.g_desc
    ((integralPairSequence_shortExact A).exact.map
      (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) (p + q)))
    (ModuleCat.ofHom (capRelativeRaw A p q))
  have hz : ((integralSubspaceChains A).f (p + q)) ≫
      ModuleCat.ofHom (capRelativeRaw A p q) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact capRelativeRaw_zero A p q b
  exact congrArg (fun f => f c phi) (h hz)

end

end PoincareConjecture.Proofs.M02.Topology
