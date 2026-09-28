import PoincareConjecture.Proofs.M02.SmallBoundaryWitness
import PoincareConjecture.Proofs.M02.IntegralCycleBoundary
import PoincareConjecture.Proofs.M02.IntegralHomologyCycle
import Mathlib.Algebra.Category.ModuleCat.EpiMono









set_option autoImplicit false

open CategoryTheory Limits

universe u v

namespace PoincareConjecture.Proofs.M02

open PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X] {I : Type v}

theorem integral_small_inclusion_homologyMap_mono_succ
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat) :
    Mono (HomologicalComplex.homologyMap (integralSmallChainInclusion U) (n + 1)) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y hxy
  let Ks := integralSmallChainComplex U
  let K := integralChains X
  let f := integralSmallChainInclusion U
  let γ : integralCoefficient ⟶ Ks.homology (n + 1) :=
    (integralCoefficientHomEquiv (Ks.homology (n + 1))).symm (x - y)
  have hγmap : γ ≫ HomologicalComplex.homologyMap f (n + 1) = 0 := by
    apply (integralCoefficientHomEquiv (K.homology (n + 1))).injective
    change (HomologicalComplex.homologyMap f (n + 1)) (γ (ULift.up 1)) = 0
    have hγeval : γ (ULift.up 1) = x - y := by
      simpa [γ] using integralCoefficientHomEquiv_symm_apply _ (x - y) (ULift.up 1)
    rw [hγeval, map_sub]
    exact sub_eq_zero.mpr hxy
  obtain ⟨aₛ, haₛ, hza⟩ := exists_integral_homology_cycle Ks n γ
  have ha_small : (aₛ ≫ f.f (n + 1)) (ULift.up 1) ∈
      integralSmallChains U (n + 1) := by
    change (aₛ (ULift.up 1)).val ∈ integralSmallChains U (n + 1)
    exact (aₛ (ULift.up 1)).property
  have ha : (aₛ ≫ f.f (n + 1)) ≫ K.d (n + 1) n = 0 := by
    rw [Category.assoc, f.comm, ← Category.assoc, haₛ, zero_comp]
  have hza0 :
      K.liftCycles (aₛ ≫ f.f (n + 1)) n (by simp) ha ≫ K.homologyπ (n + 1) = 0 := by
    have hγmap' := hγmap
    rw [← hza, Category.assoc, HomologicalComplex.homologyπ_naturality,
      ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap] at hγmap'
    exact hγmap'
  obtain ⟨b, hb⟩ := integral_cycle_boundary_of_zero_homology_class n
    (aₛ ≫ f.f (n + 1)) ha hza0
  obtain ⟨a'ₛ, b'ₛ, hb'ₛ, ha'ₛ⟩ := exists_integral_small_chain_boundary
    U hU hcover (n + 1) (aₛ ≫ f.f (n + 1)) ha ha_small ⟨b, hb⟩
  have ha'ₛ_eq : a'ₛ = aₛ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (a'ₛ ≫ f.f (n + 1)) q = (aₛ ≫ f.f (n + 1)) q
    exact congrArg (fun g => g q) ha'ₛ
  have hγzero : γ = 0 := by
    rw [← hza]
    have hboundary : aₛ = b'ₛ ≫ Ks.d (n + 2) (n + 1) := by
      simpa only [ha'ₛ_eq] using hb'ₛ.symm
    exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
      (K := Ks) aₛ n (by simp) b'ₛ hboundary
  have hxy0 : x - y = 0 := by
    have hγzero' := congrArg (integralCoefficientHomEquiv (Ks.homology (n + 1))) hγzero
    simpa [γ] using hγzero'
  exact sub_eq_zero.mp hxy0

end

end PoincareConjecture.Proofs.M02
