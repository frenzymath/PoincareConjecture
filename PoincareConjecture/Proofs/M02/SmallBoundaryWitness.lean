import PoincareConjecture.Proofs.M02.SmallHomologyRepresentative
import PoincareConjecture.Proofs.M02.IntegralChains

set_option autoImplicit false

open CategoryTheory Limits

universe u v

namespace PoincareConjecture.Proofs.M02

open PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X] {I : Type v}

theorem exists_integral_small_boundary_witness
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat)
    (a : integralCoefficient ⟶ (integralChains X).X n)
    (ha : a ≫ (integralChains X).d n (n - 1) = 0)
    (ha_small : a (ULift.up 1) ∈ integralSmallChains U n)
    (hb : ∃ b : integralCoefficient ⟶ (integralChains X).X (n + 1),
      b ≫ (integralChains X).d (n + 1) n = a) :
    ∃ b' : integralCoefficient ⟶ (integralChains X).X (n + 1),
      b' (ULift.up 1) ∈ integralSmallChains U (n + 1) ∧
      b' ≫ (integralChains X).d (n + 1) n = a := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨k, hk⟩ := integral_subdivision_eventually_small U hU hcover
    (n + 1) (b (ULift.up 1))
  let S := integralSubdivisionIterate X k
  let H := integralIteratedSubdivisionPrism X k
  let p := H.hom n (n + 1)
  let b' := b ≫ S.f (n + 1) + a ≫ p
  have hSb : (b ≫ S.f (n + 1)) (ULift.up 1) ∈
      integralSmallChains U (n + 1) := hk
  have hpa : (a ≫ p) (ULift.up 1) ∈ integralSmallChains U (n + 1) := by
    change p (a (ULift.up 1)) ∈ integralSmallChains U (n + 1)
    exact integralIteratedSubdivisionPrism_small U k n (n + 1)
      (a (ULift.up 1)) ha_small
  refine ⟨b', ?_, ?_⟩
  · change (b ≫ S.f (n + 1)) (ULift.up 1) +
      (a ≫ p) (ULift.up 1) ∈ integralSmallChains U (n + 1)
    exact (integralSmallChains U (n + 1)).add_mem hSb hpa
  · have hcomm := congrArg (fun q => a ≫ q) (H.comm n)
    rw [HomologicalComplex.id_f] at hcomm
    change b' ≫ (integralChains X).d (n + 1) n = a
    dsimp only [b', p]
    cases n with
    | zero =>
        rw [dNext_eq_zero H.hom 0 (by simp),
          prevD_eq H.hom (show (ComplexShape.down Nat).Rel 1 0 from rfl)] at hcomm
        simp only [Category.comp_id, Preadditive.comp_add, comp_zero] at hcomm
        have hcomm0 : a = a ≫ H.hom 0 1 ≫ (integralChains X).d 1 0 +
            a ≫ S.f 0 := by simpa only [zero_add] using hcomm
        rw [Preadditive.add_comp, Category.assoc, Category.assoc,
          S.comm, ← Category.assoc, hb]
        simpa only [add_comm] using hcomm0.symm
    | succ m =>
        rw [dNext_eq H.hom (show (ComplexShape.down Nat).Rel (m + 1) m from rfl),
          prevD_eq H.hom (show (ComplexShape.down Nat).Rel (m + 2) (m + 1) from rfl)] at hcomm
        simp only [Category.comp_id, Preadditive.comp_add] at hcomm
        have hcomm1 : a = a ≫ (integralChains X).d (m + 1) m ≫ H.hom m (m + 1) +
            a ≫ H.hom (m + 1) (m + 2) ≫ (integralChains X).d (m + 2) (m + 1) +
            a ≫ S.f (m + 1) := by simpa only [Nat.add_assoc] using hcomm
        rw [Preadditive.add_comp, Category.assoc, Category.assoc,
          S.comm, ← Category.assoc, hb]
        have ha' : a ≫ (integralChains X).d (m + 1) m = 0 := by
          simpa using ha
        have hcomm1' := hcomm1
        rw [← Category.assoc, ha', zero_comp] at hcomm1'
        have hcomm1'' : a =
            a ≫ H.hom (m + 1) (m + 2) ≫ (integralChains X).d (m + 2) (m + 1) +
            a ≫ S.f (m + 1) := by
          simpa only [zero_add, add_assoc] using hcomm1'
        simpa only [add_comm] using hcomm1''.symm

theorem exists_integral_small_chain_boundary
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat)
    (a : integralCoefficient ⟶ (integralChains X).X n)
    (ha : a ≫ (integralChains X).d n (n - 1) = 0)
    (ha_small : a (ULift.up 1) ∈ integralSmallChains U n)
    (hb : ∃ b : integralCoefficient ⟶ (integralChains X).X (n + 1),
      b ≫ (integralChains X).d (n + 1) n = a) :
    ∃ aₛ : integralCoefficient ⟶ (integralSmallChainComplex U).X n,
      ∃ bₛ : integralCoefficient ⟶ (integralSmallChainComplex U).X (n + 1),
        bₛ ≫ (integralSmallChainComplex U).d (n + 1) n = aₛ ∧
        aₛ ≫ (integralSmallChainInclusion U).f n = a := by
  obtain ⟨b', hb'small, hb'⟩ := exists_integral_small_boundary_witness
    U hU hcover n a ha ha_small hb
  have hsmall_all (m : Nat) (q : integralCoefficient ⟶ (integralChains X).X m)
      (hq : q (ULift.up 1) ∈ integralSmallChains U m) (z : ULift.{u} Int) :
      q z ∈ integralSmallChains U m := by
    have hz : z = z.down • (ULift.up 1 : ULift.{u} Int) := by
      apply ULift.ext
      simp
    rw [hz, map_zsmul]
    exact (integralSmallChains U m).toAddSubgroup.zsmul_mem hq z.down
  let : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
  let : Module Int (integralSmallChains U (n + 1)) :=
    (integralSmallChains U (n + 1)).module
  let haₛ : integralCoefficient ⟶ (integralSmallChainComplex U).X n :=
    ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U n) a.hom
      (hsmall_all n a ha_small))
  let hbₛ : integralCoefficient ⟶ (integralSmallChainComplex U).X (n + 1) :=
    ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U (n + 1)) b'.hom
      (hsmall_all (n + 1) b' hb'small))
  refine ⟨haₛ, hbₛ, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change (b' ≫ (integralChains X).d (n + 1) n) z = a z
    exact congrArg (fun q => q z) hb'
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change a z = a z
    rfl

end

end PoincareConjecture.Proofs.M02
