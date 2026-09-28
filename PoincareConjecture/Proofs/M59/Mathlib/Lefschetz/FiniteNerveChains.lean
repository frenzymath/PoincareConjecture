import PoincareConjecture.Proofs.M02.Topology.IntegralChainCoordinates
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

def normalizedIntegralChainCoordinates (X : SSet.{u}) (n : ℕ) :
    (X.normalizedChainComplex integralCoefficient).X n ≃ₗ[ℤ]
      (X.nonDegenerate n →₀ ℤ) :=
  let e := (X.isColimitCofanNormalizedChainComplex integralCoefficient n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (X.nonDegenerate n))
  e.toLinearEquiv.trans (Finsupp.mapRange.linearEquiv ULift.moduleEquiv)

theorem normalizedIntegralChainCoordinates_generator (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) (a : ℤ) :
    normalizedIntegralChainCoordinates X n
      (X.ιNormalizedChainComplex (R := integralCoefficient) s.val (ULift.up a)) =
        Finsupp.single s a := by
  let e := (X.isColimitCofanNormalizedChainComplex integralCoefficient n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (X.nonDegenerate n))
  have hι := IsColimit.comp_coconePointUniqueUpToIso_hom
    (X.isColimitCofanNormalizedChainComplex integralCoefficient n)
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (X.nonDegenerate n))
    (Discrete.mk s)
  have he : e.hom (X.ιNormalizedChainComplex (R := integralCoefficient) s.val (ULift.up a)) =
      Finsupp.single s (ULift.up a) := congrArg (fun f => f (ULift.up a)) hι
  change Finsupp.mapRange.linearEquiv ULift.moduleEquiv
    (e.hom (X.ιNormalizedChainComplex (R := integralCoefficient) s.val (ULift.up a))) =
      Finsupp.single s a
  rw [he]
  simp only [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single]
  rfl

def normalizedIntegralChainBasis (X : SSet.{u}) (n : ℕ) :
    Module.Basis (X.nonDegenerate n) ℤ
      ((X.normalizedChainComplex integralCoefficient).X n) :=
  Finsupp.basisSingleOne.map (normalizedIntegralChainCoordinates X n).symm

theorem normalizedIntegralChainBasis_apply (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) :
    normalizedIntegralChainBasis X n s =
      X.ιNormalizedChainComplex (R := integralCoefficient) s.val (ULift.up 1) := by
  apply (normalizedIntegralChainCoordinates X n).injective
  rw [normalizedIntegralChainCoordinates_generator]
  simp only [normalizedIntegralChainBasis, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, Finsupp.coe_basisSingleOne]

theorem normalizedIntegralChain_finite (X : SSet.{u}) (n : ℕ)
    [Finite (X.nonDegenerate n)] :
    Module.Finite ℤ ((X.normalizedChainComplex integralCoefficient.{u}).X n) := by
  let := Fintype.ofFinite (X.nonDegenerate n)
  exact Module.Finite.of_basis (normalizedIntegralChainBasis X n)

theorem normalizedIntegralChain_free (X : SSet.{u}) (n : ℕ) :
    Module.Free ℤ ((X.normalizedChainComplex integralCoefficient.{u}).X n) :=
  Module.Free.of_basis (normalizedIntegralChainBasis X n)

theorem finite_nerve_nonDegenerate (J : Type u) [PartialOrder J] [Finite J] (n : ℕ) :
    Finite ((nerve J).nonDegenerate n) := by
  apply Finite.of_injective (fun s : (nerve J).nonDegenerate n => s.val.obj)
  intro s t h
  apply Subtype.ext
  exact nerve.ext_of_isThin h

theorem nerve_nonDegenerate_dim_lt (J : Type u) [PartialOrder J] [Fintype J]
    {n : ℕ} (s : (nerve J).nonDegenerate n) : n < Fintype.card J := by
  have hi := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property
  have h := Fintype.card_le_of_injective s.val.obj hi
  simpa only [Fintype.card_fin, Nat.succ_le_iff] using h

theorem finite_nerve_normalizedChain_isZero (J : Type u) [PartialOrder J] [Fintype J]
    (n : ℕ) (hn : Fintype.card J ≤ n) :
    IsZero (((nerve J).normalizedChainComplex integralCoefficient.{u}).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hempty : IsEmpty ((nerve J).nonDegenerate n) :=
    ⟨fun s => (Nat.not_lt_of_ge hn) (nerve_nonDegenerate_dim_lt J s)⟩
  exact (normalizedIntegralChainCoordinates (nerve J) n).injective.subsingleton

end PoincareConjecture.Proofs.M59
