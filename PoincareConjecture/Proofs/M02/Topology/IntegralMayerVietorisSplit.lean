import PoincareConjecture.Proofs.M02.Topology.IntegralSupportMayerVietoris
import PoincareConjecture.Proofs.M02.Topology.IntegralCochains

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set
open scoped BigOperators

universe u

namespace PoincareConjecture.Proofs.M02.Topology

attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Submodule.Quotient.module

variable {X : Type u} [TopologicalSpace X]

def integralSumChainFilter (A B : Set X) (n : Nat) :
    (integralChains X).X n →ₗ[Int] (integralChains X).X n := by
  classical
  exact (Finsupp.lsum Nat (fun s : C(integralSimplex n, X) =>
    if range s ⊆ A ∨ range s ⊆ B then 0 else (integralSingularGenerator s).hom)).comp
      (integralChainCoordinates X n).toLinearMap

@[simp]
theorem integralSumChainFilter_generator (A B : Set X) {n : Nat}
    (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
    integralSumChainFilter A B n (integralSingularGenerator s a) =
      if range s ⊆ A ∨ range s ⊆ B then 0 else integralSingularGenerator s a := by
  classical
  change (Finsupp.lsum Nat (fun t : C(integralSimplex n, X) =>
    if range t ⊆ A ∨ range t ⊆ B then 0 else (integralSingularGenerator t).hom))
      (integralChainCoordinates X n (integralSingularGenerator s a)) = _
  rw [integralChainCoordinates_generator, Finsupp.lsum_single]
  split_ifs <;> rfl

theorem integralSumChainFilter_subspace_zero (A B : Set X) (n : Nat)
    (c : (integralChains X).X n)
    (hc : c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom ∨
      c ∈ LinearMap.range ((integralSubspaceChains B).f n).hom) :
    integralSumChainFilter A B n c = 0 := by
  classical
  rw [integral_chain_finite_representation n c, map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [integralSumChainFilter_generator, if_pos]
  rcases hc with hc | hc
  · exact Or.inl ((integral_subspace_range_iff A n c).mp hc s hs)
  · exact Or.inr ((integral_subspace_range_iff B n c).mp hc s hs)

theorem integralSumChainFilter_projection (A B : Set X) (n : Nat)
    (c : (integralChains X).X n) :
    (integralSumAmbientProjection A B).f n (integralSumChainFilter A B n c) =
      (integralSumAmbientProjection A B).f n c := by
  classical
  rw [integral_chain_finite_representation n c, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integralSumChainFilter_generator]
  by_cases h : range s ⊆ A ∨ range s ⊆ B
  · rw [if_pos h, map_zero]
    symm
    rcases h with hA | hB
    · obtain ⟨a, ha⟩ := integralSingularGenerator_mem_subspace A s hA
        (integralChainCoordinates X n c s)
      rw [← ha]
      exact congrArg (fun f => f.f n a) (integralSubspace_sumAmbientProjection_left A B)
    · obtain ⟨b, hb⟩ := integralSingularGenerator_mem_subspace B s hB
        (integralChainCoordinates X n c s)
      rw [← hb]
      exact congrArg (fun f => f.f n b) (integralSubspace_sumAmbientProjection_right A B)
  · rw [if_neg h]

theorem integralSumAmbientProjection_surjective (A B : Set X) (n : Nat) :
    Function.Surjective ((integralSumAmbientProjection A B).f n) :=
  (integralProjection_surjective (integralPairInclusion A B) n).comp
    (integralProjection_surjective (integralSubspaceChains A) n)

def integralSumQuotientSection (A B : Set X) (n : Nat) :
    (integralSumQuotient A B).X n →ₗ[Int] (integralChains X).X n := by
  let p := ((integralSumAmbientProjection A B).f n).hom
  let F := integralSumChainFilter A B n
  have hker : LinearMap.ker p ≤ LinearMap.ker F := by
    intro c hc
    obtain ⟨a, b, rfl⟩ := (integralSumAmbientProjection_eq_zero_iff A B n c).mp hc
    rw [LinearMap.mem_ker, map_add]
    rw [integralSumChainFilter_subspace_zero A B n _ (Or.inl ⟨a, rfl⟩),
      integralSumChainFilter_subspace_zero A B n _ (Or.inr ⟨b, rfl⟩), add_zero]
  exact ((LinearMap.ker p).liftQ F hker).comp
    (p.quotKerEquivOfSurjective (integralSumAmbientProjection_surjective A B n)).symm.toLinearMap

@[simp]
theorem integralSumQuotientSection_projection (A B : Set X) (n : Nat)
    (c : (integralChains X).X n) :
    integralSumQuotientSection A B n ((integralSumAmbientProjection A B).f n c) =
      integralSumChainFilter A B n c := by
  simp [integralSumQuotientSection]

theorem integralSumQuotientSection_rightInverse (A B : Set X) (n : Nat)
    (c : (integralSumQuotient A B).X n) :
    (integralSumAmbientProjection A B).f n (integralSumQuotientSection A B n c) = c := by
  obtain ⟨b, rfl⟩ := integralSumAmbientProjection_surjective A B n c
  rw [integralSumQuotientSection_projection, integralSumChainFilter_projection]

def integralSupportDegreeSplitting (K L : Set X) (n : Nat) :
    ((integralSupportIntermediateSequence K L).map
      (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)).Splitting := by
  let S := (integralSupportIntermediateSequence K L).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)
  have hS : S.ShortExact := (integralSupportIntermediateSequence_shortExact K L).map_of_exact _
  let s : S.X₃ ⟶ S.X₂ := ModuleCat.ofHom (integralSumQuotientSection Kᶜ Lᶜ n) ≫
    (integralRelativeProjection Kᶜ).f n ≫
      (biprod.inl : integralRelativeChains Kᶜ ⟶
        integralRelativeChains Kᶜ ⊞ integralRelativeChains Lᶜ).f n
  have hs : s ≫ S.g = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    have hg := congrArg (fun f => f.f n
      ((integralRelativeProjection Kᶜ).f n (integralSumQuotientSection Kᶜ Lᶜ n c)))
        (biprod.inl_desc (integralSumProjection Kᶜ Lᶜ)
          (-integralSumRightProjection Kᶜ Lᶜ))
    change (integralSumDifference Kᶜ Lᶜ).f n
        ((biprod.inl : integralRelativeChains Kᶜ ⟶
          integralRelativeChains Kᶜ ⊞ integralRelativeChains Lᶜ).f n
            ((integralRelativeProjection Kᶜ).f n (integralSumQuotientSection Kᶜ Lᶜ n c))) =
      (integralSumProjection Kᶜ Lᶜ).f n
        ((integralRelativeProjection Kᶜ).f n (integralSumQuotientSection Kᶜ Lᶜ n c)) at hg
    exact hg.trans (integralSumQuotientSection_rightInverse Kᶜ Lᶜ n c)
  exact ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f

theorem integralSupportIntermediateSequence_degreewiseSplit (K L : Set X) :
    IntegralDegreewiseSplit (integralSupportIntermediateSequence K L) := by
  intro n
  let s := integralSupportDegreeSplitting K L n
  exact ⟨s.r, s.s, s.f_r, s.s_g, s.id⟩

theorem integralSupportDualSequence_shortExact (K L : Set X) :
    (integralDualSequence (integralSupportIntermediateSequence K L)).ShortExact :=
  integralDualSequence_shortExact _ (integralSupportIntermediateSequence_degreewiseSplit K L)

end PoincareConjecture.Proofs.M02.Topology
