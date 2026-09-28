import PoincareConjecture.Proofs.M02.Topology.IntegralChainCoordinates

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] {I : Type v}

def IntegralSmallSimplex (U : I → Set X) {n : Nat}
    (s : C(integralSimplex n, X)) : Prop :=
  ∃ i, Set.range s ⊆ U i

def integralSmallChains (U : I → Set X) (n : Nat) :
    Submodule Int ((integralChains X).X n) :=
  Submodule.span Int (Set.range (fun s : {s : C(integralSimplex n, X) //
    IntegralSmallSimplex U s} => integralSingularGenerator s.val (ULift.up 1)))

def integralSmallChainComplex (U : I → Set X) :
    ChainComplex (ModuleCat.{u} Int) Nat := by
  have hpres (i j : Nat) (c : integralSmallChains U i) :
      (integralChains X).d i j c.val ∈ integralSmallChains U j := by
    by_cases hij : (ComplexShape.down Nat).Rel i j
    · change j + 1 = i at hij
      subst i
      have hle : integralSmallChains U (j + 1) ≤
          (integralSmallChains U j).comap ((integralChains X).d (j + 1) j).hom := by
        apply Submodule.span_le.mpr
        rintro _ ⟨s, rfl⟩
        change (integralChains X).d (j + 1) j
          (integralSingularGenerator s.val (ULift.up 1)) ∈ integralSmallChains U j
        let ev : (integralCoefficient.{u} ⟶ (integralChains X).X j) →+
            (integralChains X).X j :=
          { toFun := fun f => f (ULift.up 1)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have he := congrArg ev (integralSingularGenerator_boundary s.val)
        rw [map_sum] at he
        change (integralChains X).d (j + 1) j
          (integralSingularGenerator s.val (ULift.up 1)) = _ at he
        rw [he]
        apply Submodule.sum_mem
        intro k _
        rw [map_zsmul]
        apply (integralSmallChains U j).toAddSubgroup.zsmul_mem
        change integralSingularGenerator (s.val.comp (integralSimplexFace j k))
          (ULift.up 1) ∈ integralSmallChains U j
        apply Submodule.subset_span
        refine ⟨⟨s.val.comp (integralSimplexFace j k), ?_⟩, rfl⟩
        rcases s.property with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rintro _ ⟨z, rfl⟩
        exact ha ⟨integralSimplexFace j k z, rfl⟩
      exact hle c.property
    · rw [(integralChains X).shape i j hij]
      exact (integralSmallChains U j).zero_mem
  let C : Nat → ModuleCat.{u} Int := fun n =>
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    ModuleCat.of Int (integralSmallChains U n)
  let d (i j : Nat) : C i ⟶ C j := by
    letI : Module Int (integralSmallChains U i) := (integralSmallChains U i).module
    letI : Module Int (integralSmallChains U j) := (integralSmallChains U j).module
    exact ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U j)
      (((integralChains X).d i j).hom.domRestrict (integralSmallChains U i)) (hpres i j))
  refine { X := C, d := d, shape := ?_, d_comp_d' := ?_ }
  · intro i j hij
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (integralChains X).d i j c.val = 0
    rw [(integralChains X).shape i j hij]
    rfl
  · intro i j k _ _
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (integralChains X).d j k ((integralChains X).d i j c.val) = 0
    exact congrArg (fun f : (integralChains X).X i ⟶ (integralChains X).X k =>
      f c.val) ((integralChains X).d_comp_d i j k)

def integralSmallChainInclusion (U : I → Set X) :
    integralSmallChainComplex U ⟶ integralChains X where
  f n := by
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    exact ModuleCat.ofHom (integralSmallChains U n).subtype
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

theorem integralSmallChainInclusion_mono (U : I → Set X) :
    Mono (integralSmallChainInclusion U) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b h
  exact Subtype.ext h

end PoincareConjecture.Proofs.M02.Topology
