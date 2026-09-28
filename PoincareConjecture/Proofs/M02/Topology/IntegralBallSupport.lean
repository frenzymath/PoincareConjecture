import PoincareConjecture.Proofs.M02.Topology.ClosedBallComplement
import PoincareConjecture.Proofs.M02.Topology.IntegralSphereVanishing
import PoincareConjecture.Proofs.M02.Topology.IntegralSphereBase
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option autoImplicit false

open CategoryTheory Limits Metric HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

def integralBallToPointRestriction (c : E) (r : Real) (hr : 0 ≤ r) :
    integralRelativeChains ((closedBall c r)ᶜ : Set E) ⟶
      integralRelativeChains ({c}ᶜ : Set E) :=
  integralRelativeMap (ContinuousMap.id E)
    (show Set.MapsTo (ContinuousMap.id E) ((closedBall c r)ᶜ) ({c}ᶜ : Set E) from
      fun ⦃x⦄ hx => by
        rw [ContinuousMap.id_apply]
        exact closedBallComplement_subset_puncture c r hr hx)

theorem integralBallToPointRestriction_quasiIso (c : E) (r : Real) (hr : 0 ≤ r) :
    QuasiIso (integralBallToPointRestriction c r hr) := by
  let O : Set E := (closedBall c r)ᶜ
  let P : Set E := {c}ᶜ
  let I : integralChains O ⟶ integralChains P :=
    integralChainsFunctor.map (TopCat.ofHom (closedBallComplementInclusion c r hr))
  have hI : QuasiIso I := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (integralHomologyIsoOfHomotopyEquiv
      (closedBallComplementPunctureHomotopyEquiv c r hr) n).hom
    infer_instance
  let F : integralPairSequence O ⟶ integralPairSequence P :=
    { τ₁ := I
      τ₂ := 𝟙 (integralChains E)
      τ₃ := integralBallToPointRestriction c r hr
      comm₁₂ := by
        change I ≫ integralSubspaceChains P = integralSubspaceChains O ≫ 𝟙 _
        rw [Category.comp_id]
        dsimp only [I, integralSubspaceChains]
        rw [← Functor.map_comp]
        rfl
      comm₂₃ := by
        change 𝟙 _ ≫ integralRelativeProjection P =
          integralRelativeProjection O ≫ integralRelativeMap (ContinuousMap.id E) _
        rw [Category.id_comp, integralRelativeMap_projection]
        change integralRelativeProjection P =
          integralChainsFunctor.map (𝟙 (TopCat.of E)) ≫ integralRelativeProjection P
        simp }
  exact HomologySequence.quasiIso_τ₃ F
    (integralPairSequence_shortExact O) (integralPairSequence_shortExact P) hI
      (by change QuasiIso (𝟙 (integralChains E)); infer_instance)

theorem integralBallToPointRestriction_homologyMap_isIso
    (c : E) (r : Real) (hr : 0 ≤ r) (n : Nat) :
    IsIso (homologyMap (integralBallToPointRestriction c r hr) n) := by
  let := integralBallToPointRestriction_quasiIso c r hr
  infer_instance

def integralEuclideanBallSupportThreeIso
    (c : EuclideanSpace Real (Fin 3)) (r : Real) (hr : 0 ≤ r) :
    integralRelativeHomology ((closedBall c r)ᶜ : Set (EuclideanSpace Real (Fin 3))) 3 ≅
      integralCoefficient :=
  integralContractibleAmbientRelativeBoundaryIso ((closedBall c r)ᶜ) 1 ≪≫
    integralHomologyIsoOfHomotopyEquiv
      (closedBallComplementSphereHomotopyEquiv c r hr) 2 ≪≫ integralSphereH2Iso

theorem integralEuclideanBallSupportFour_isZero
    (c : EuclideanSpace Real (Fin 3)) (r : Real) (hr : 0 ≤ r) :
    IsZero (integralRelativeHomology
      ((closedBall c r)ᶜ : Set (EuclideanSpace Real (Fin 3))) 4) :=
  integralSphereS2HomologyThree_isZero.of_iso
    (integralContractibleAmbientRelativeBoundaryIso ((closedBall c r)ᶜ) 2 ≪≫
      integralHomologyIsoOfHomotopyEquiv
        (closedBallComplementSphereHomotopyEquiv c r hr) 3)

end

end PoincareConjecture.Proofs.M02.Topology
