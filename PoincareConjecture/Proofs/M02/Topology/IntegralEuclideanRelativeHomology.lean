import PoincareConjecture.Proofs.M02.Topology.IntegralConvexSupport
import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyZero
import PoincareConjecture.Proofs.M02.Topology.IntegralBallSupport
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Metric Set
open scoped ContinuousMap

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem integralHomologyZeroMap_isIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    IsIso (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0) := by
  let := integralHomologyZeroAugmentation_isIso X
  let := integralHomologyZeroAugmentation_isIso Y
  have he : homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0 =
      integralHomologyZeroAugmentation X ≫ inv (integralHomologyZeroAugmentation Y) := by
    apply (cancel_mono (integralHomologyZeroAugmentation Y)).mp
    rw [integralHomologyZeroAugmentation_natural, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  rw [he]
  infer_instance

theorem integralSphereS2HomologyOne_isZero :
    IsZero (integralHomology (sphere (0 : EuclideanSpace Real (Fin 3)) 1) 1) := by
  obtain ⟨A, B, hA, hB, hcover, hAc, hBc, ⟨hAB⟩⟩ :=
    exists_sphere_contractible_open_cover 1
  let : ContractibleSpace A := hAc
  let : ContractibleSpace B := hBc
  let AB : Set B := (Subtype.val : B → sphere (0 : EuclideanSpace Real (Fin 3)) 1) ⁻¹' A
  let e : AB ≃ₕ sphere (0 : EuclideanSpace Real (Fin 2)) 1 :=
    ((intersectionPreimageHomeomorph A B).symm.toHomotopyEquiv).trans hAB
  let : PathConnectedSpace (sphere (0 : EuclideanSpace Real (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  let := integralHomologyZeroAugmentation_isIso
    (sphere (0 : EuclideanSpace Real (Fin 2)) 1)
  let eH := integralHomologyIsoOfHomotopyEquiv e 0
  have haug : IsIso (integralHomologyZeroAugmentation AB) := by
    rw [← integralHomologyZeroAugmentation_natural e.toFun]
    change IsIso (eH.hom ≫ _)
    infer_instance
  let := haug
  exact (isZero_kernel_of_mono (integralHomologyZeroAugmentation AB)).of_iso
    (integralContractibleCoverHomologyOneIso A B hA hB hcover ≪≫
      integralHomologyZeroMapKernelIso (⟨Subtype.val, continuous_subtype_val⟩ : C(AB, B)))

theorem integralPuncturedEuclideanRelativeLow_isZero (n : Nat) (hn : n < 3) :
    IsZero (integralRelativeHomology
      ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) n) := by
  let E := EuclideanSpace Real (Fin 3)
  let A : Set E := {0}ᶜ
  let : PathConnectedSpace A := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_compl_singleton_of_one_lt_rank
      (Module.one_lt_rank_of_one_lt_finrank (by simp [E])) (0 : E))
  let : IsIso (homologyMap (integralSubspaceChains A) 0) :=
    integralHomologyZeroMap_isIso (⟨Subtype.val, continuous_subtype_val⟩ : C(A, E))
  let S := integralPairSequence_shortExact A
  interval_cases n
  · apply (exactAt_iff_isZero_homology _ _).mp
    refine S.exactAt_X₃ 0 ?_ ?_
    · change Epi (homologyMap (integralSubspaceChains A) 0)
      infer_instance
    · intro j hj
      exact False.elim (by change j + 1 = 0 at hj; omega)
  · apply (exactAt_iff_isZero_homology _ _).mp
    refine S.exactAt_X₃ 1 ?_ ?_
    · exact (integral_contractible_homology_isZero E 1 (by decide)).epi _
    · intro j hj
      have hj0 : j = 0 := by change j + 1 = 1 at hj; omega
      subst j
      change Mono (homologyMap (integralSubspaceChains A) 0)
      infer_instance
  · exact integralSphereS2HomologyOne_isZero.of_iso
      (integralContractibleAmbientRelativeBoundaryIso A 0 ≪≫
        integralHomologyIsoOfHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E) 1)

theorem integralPuncturedEuclideanRelative_ne_three_isZero (n : Nat) (hn : n ≠ 3) :
    IsZero (integralRelativeHomology
      ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) n) := by
  by_cases hlow : n < 3
  · exact integralPuncturedEuclideanRelativeLow_isZero n hlow
  · obtain ⟨k, rfl⟩ : ∃ k : Nat, n = k + 4 := ⟨n - 4, by omega⟩
    exact integralPuncturedEuclideanRelativeAbove_isZero k

theorem integralEuclideanZeroBallHomology_ne_three_isZero
    (r : Real) (hr : 0 ≤ r) (n : Nat) (hn : n ≠ 3) :
    IsZero (integralSupportHomology
      (closedBall (0 : EuclideanSpace Real (Fin 3)) r) n) := by
  let := integralBallToPointRestriction_homologyMap_isIso
    (0 : EuclideanSpace Real (Fin 3)) r hr n
  exact (integralPuncturedEuclideanRelative_ne_three_isZero n hn).of_iso
    (asIso (homologyMap (integralBallToPointRestriction
      (0 : EuclideanSpace Real (Fin 3)) r hr) n))

end PoincareConjecture.Proofs.M02.Topology
