import PoincareConjecture.Proofs.M02.SmallHomologyRepresentative
import PoincareConjecture.Proofs.M02.IntegralHomologyCycle
import Mathlib.Algebra.Category.ModuleCat.EpiMono

set_option autoImplicit false

open CategoryTheory Limits

universe u v

namespace PoincareConjecture.Proofs.M02

open PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X] {I : Type v}

theorem integral_small_inclusion_homologyMap_epi_succ
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat) :
    Epi (HomologicalComplex.homologyMap (integralSmallChainInclusion U) (n + 1)) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  let K := integralChains X
  let Ks := integralSmallChainComplex U
  let f := integralSmallChainInclusion U
  let γ : integralCoefficient ⟶ K.homology (n + 1) :=
    (integralCoefficientHomEquiv (K.homology (n + 1))).symm y
  obtain ⟨c, hc, hγ⟩ := exists_integral_homology_cycle K n γ
  obtain ⟨k, hk, hck, hclass⟩ := exists_integral_small_homology_representative
    U hU hcover n c hc
  let c' := c ≫ (integralSubdivisionIterate X k).f (n + 1)
  have hc' : c' ≫ K.d (n + 1) n = 0 := by
    exact hck
  have hc'small : c' (ULift.up 1) ∈ integralSmallChains U (n + 1) := hk
  have hsmall_all (z : ULift.{u} Int) :
      c' z ∈ integralSmallChains U (n + 1) := by
    have hz : z = z.down • (ULift.up 1 : ULift.{u} Int) := by
      apply ULift.ext
      simp
    rw [hz, map_zsmul]
    exact (integralSmallChains U (n + 1)).toAddSubgroup.zsmul_mem hc'small z.down
  let : Module Int (integralSmallChains U (n + 1)) :=
    (integralSmallChains U (n + 1)).module
  let cₛ : integralCoefficient ⟶ Ks.X (n + 1) :=
    ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U (n + 1)) c'.hom
      hsmall_all)
  have hcₛ : cₛ ≫ Ks.d (n + 1) n = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change (c' ≫ K.d (n + 1) n) z = 0
    exact congrArg (fun g => g z) hc'
  have hcₛ_incl : cₛ ≫ f.f (n + 1) = c' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  have hliftcomp :
      K.liftCycles (cₛ ≫ f.f (n + 1)) n (by simp)
          (by rw [Category.assoc, f.comm, ← Category.assoc, hcₛ, zero_comp]) =
        K.liftCycles c' n (by simp) hc' := by
    apply (cancel_mono (K.iCycles (n + 1))).mp
    rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i,
      hcₛ_incl]
  let γₛ := Ks.liftCycles cₛ n (by simp) hcₛ ≫ Ks.homologyπ (n + 1)
  have hγₛmap : γₛ ≫ HomologicalComplex.homologyMap f (n + 1) = γ := by
    dsimp only [γₛ]
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
      ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap,
      hliftcomp, hclass.symm, hγ]
  refine ⟨γₛ (ULift.up 1), ?_⟩
  have hγeval : γ (ULift.up 1) = y := by
    simpa [γ] using integralCoefficientHomEquiv_symm_apply _ y (ULift.up 1)
  have hmap_eval := congrArg (fun g => g (ULift.up 1)) hγₛmap
  change (HomologicalComplex.homologyMap f (n + 1)) (γₛ (ULift.up 1)) = y
  exact hmap_eval.trans hγeval

end

end PoincareConjecture.Proofs.M02
