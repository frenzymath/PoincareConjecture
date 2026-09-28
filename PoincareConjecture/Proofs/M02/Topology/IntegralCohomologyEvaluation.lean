import PoincareConjecture.Proofs.M02.Topology.IntegralDualSingle









set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

attribute [local instance 2000] Submodule.Quotient.module
attribute [local instance 2000] Submodule.module

theorem integralHomologyCohomologyPairing_cycles
    (C : ChainComplex (ModuleCat.{u} Int) Nat) (d : Nat)
    (z : C.cycles d) (phi : (integralDualComplex C).cycles d) :
    integralHomologyCohomologyPairing C d (C.homologyπ d z)
        ((integralDualComplex C).homologyπ d phi) =
      (show C.X d ⟶ integralCoefficient from (integralDualComplex C).iCycles d phi)
        (C.iCycles d z) := by
  have hz := congrArg (fun f => f z) (C.sc d).π_moduleCatCyclesIso_hom
  have hp := congrArg (fun f => f phi)
    ((integralDualComplex C).sc d).π_moduleCatCyclesIso_hom
  change (C.sc d).moduleCatHomologyIso.toLinearEquiv (C.homologyπ d z) = _ at hz
  change ((integralDualComplex C).sc d).moduleCatHomologyIso.toLinearEquiv
    ((integralDualComplex C).homologyπ d phi) = _ at hp
  unfold integralHomologyCohomologyPairing
  erw [LinearMap.comp_apply, LinearMap.compl₂_apply, hz, hp]
  change (show C.X d ⟶ integralCoefficient from
      (((integralDualComplex C).sc d).moduleCatCyclesIso.hom phi).val)
      (((C.sc d).moduleCatCyclesIso.hom z).val) = _
  have hzi := congrArg (fun f => f z) (C.sc d).moduleCatCyclesIso_hom_i
  have hpi := congrArg (fun f => f phi)
    ((integralDualComplex C).sc d).moduleCatCyclesIso_hom_i
  change (((C.sc d).moduleCatCyclesIso.hom z).val) = C.iCycles d z at hzi
  change (((integralDualComplex C).sc d).moduleCatCyclesIso.hom phi).val =
    (integralDualComplex C).iCycles d phi at hpi
  rw [hzi, hpi]

variable (C : ChainComplex (ModuleCat.{u} Int) Nat) (d : Nat)
  [CategoryTheory.Projective (C.homology d)]
  [∀ n, CategoryTheory.Projective (C.X n)]
  (hC : ∀ n : Nat, n ≠ d → IsZero (C.homology n))

theorem moduleComplexDualHomologyIso_pairing
    (a : C.homology d) (b : (integralDualComplex C).homology d) :
    (moduleComplexDualHomologyIso d C hC).hom b a =
      integralHomologyCohomologyPairing C d a b := by
  obtain ⟨phi, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralDualComplex C).homologyπ d)).mp inferInstance b
  have he := congrArg (fun f => f phi) (moduleComplexDualHomologyIso_projection d C hC)
  change (moduleComplexDualHomologyIso d C hC).hom
      ((integralDualComplex C).homologyπ d phi) =
    (moduleComplexHomologySection C d ≫ C.iCycles d) ≫
      ((integralDualComplex C).iCycles d phi) at he
  rw [he]
  have hs := congrArg (fun f => f a) (moduleComplexHomologySection_projection C d)
  change C.homologyπ d (moduleComplexHomologySection C d a) = a at hs
  have hp := integralHomologyCohomologyPairing_cycles C d
    (moduleComplexHomologySection C d a) phi
  rw [hs] at hp
  exact hp.symm

def integralCohomologyEvaluationEquiv :
    (integralDualComplex C).homology d ≃ₗ[Int]
      (C.homology d →ₗ[Int] ULift.{u} Int) :=
  (moduleComplexDualHomologyIso d C hC).toLinearEquiv.trans ModuleCat.homLinearEquiv

theorem integralCohomologyEvaluationEquiv_apply
    (b : (integralDualComplex C).homology d) (a : C.homology d) :
    integralCohomologyEvaluationEquiv C d hC b a =
      integralHomologyCohomologyPairing C d a b :=
  moduleComplexDualHomologyIso_pairing C d hC a b

end PoincareConjecture.Proofs.M02.Topology
