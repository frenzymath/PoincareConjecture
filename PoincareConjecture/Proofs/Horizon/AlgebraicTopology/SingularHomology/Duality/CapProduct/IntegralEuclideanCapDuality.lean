import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapEvaluation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CompactSupport.IntegralCompactSupportCap
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Euclidean.IntegralEuclideanCompactCohomology


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Metric Set TopologicalSpace

namespace Poincare.Topology

private abbrev E := EuclideanSpace Real (Fin 3)

variable (hD : ∀ L : Set E, IsCompact L → IntegralSupportDetected L 3)
  (omega : ∀ x : E, integralSupportHomology ({x} : Set E) 3)
  (hlocal : ∀ x : E, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3,
      ∀ y : E, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y)

theorem integralEuclideanCompactSupportCapOne_epi :
    Epi (integralCompactSupportCapOne hD omega hlocal) :=
  (integral_contractible_homology_isZero E 2 (by decide)).epi _

theorem integralEuclideanCompactSupportCapTwo_isIso :
    IsIso (integralCompactSupportCapTwo hD omega hlocal) := by
  have hS := integralEuclideanCompactSupportCohomology_ne_three_isZero 2 (by decide)
  have hT := integral_contractible_homology_isZero E 1 (by decide)
  let : Mono (integralCompactSupportCapTwo hD omega hlocal) := hS.mono _
  let : Epi (integralCompactSupportCapTwo hD omega hlocal) := hT.epi _
  exact isIso_of_mono_of_epi _

theorem integralEuclideanCompactSupportCapThree_isIso
    (hgen : ∃ e : Int ≃ₗ[Int] integralSupportHomology ({0} : Set E) 3,
      e 1 = omega 0) :
    IsIso (integralCompactSupportCapThree hD omega hlocal) := by
  let K := integralEuclideanZeroBallCompact 1
  have h0 : (0 : E) ∈ (K : Set E) := mem_closedBall_self (by norm_num)
  let r := integralSupportHomologyRestriction (singleton_subset_iff.mpr h0) 3
  let : IsIso r := integralCompactConvexSupportRestriction_homology_isIso
    (closedBall (0 : E) 1) (isCompact_closedBall _ _) (convex_closedBall _ _) 0 h0 3
  obtain ⟨e, he⟩ := hgen
  let eK : Int ≃ₗ[Int] integralSupportHomology (K : Set E) 3 :=
    e.trans (asIso r).symm.toLinearEquiv
  have heK : eK 1 = integralCompactSupportOrientation hD omega K hlocal := by
    apply (ModuleCat.mono_iff_injective r).mp inferInstance
    change r ((asIso r).inv (e 1)) =
      integralSupportHomologyRestriction (singleton_subset_iff.mpr h0) 3
        (integralCompactSupportOrientation hD omega K hlocal)
    rw [integralCompactSupportOrientation_spec hD omega K hlocal 0 h0, he]
    exact (asIso r).inv_hom_id_apply _
  let ev : integralSupportCohomology (K : Set E) 3 ≃ₗ[Int] ULift Int :=
    (integralEuclideanZeroBallCohomologyEvaluationEquiv 1 (by norm_num)).trans
      ((LinearEquiv.arrowCongr eK.symm (LinearEquiv.refl Int (ULift Int))).trans
        (LinearMap.ringLmapEquivSelf Int Int (ULift Int)))
  have hev (phi : integralSupportCohomology (K : Set E) 3) :
      ev phi = integralHomologyCohomologyPairing (integralSupportChains (K : Set E)) 3
        (integralCompactSupportOrientation hD omega K hlocal) phi := by
    change integralEuclideanZeroBallCohomologyEvaluationEquiv 1 (by norm_num) phi (eK 1) = _
    exact (integralEuclideanZeroBallCohomologyEvaluationEquiv_apply 1 (by norm_num)
      phi (eK 1)).trans (congrArg
        (fun a => integralHomologyCohomologyPairing (integralSupportChains (K : Set E)) 3 a phi)
          heK)
  have hcomp : integralCompactSupportCohomologyClass K 3 ≫
      integralCompactSupportCapThree hD omega hlocal ≫ integralHomologyZeroAugmentation E =
        ModuleCat.ofHom ev.toLinearMap := by
    rw [integralCompactSupportCapThree_class_assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change integralHomologyZeroAugmentation E
      (integralSupportCapHomologyThree (K : Set E)ᶜ
        (integralCompactSupportOrientation hD omega K hlocal) phi) = ev phi
    rw [integralSupportCapHomologyThree_augmentation, hev]
  let := integralEuclideanZeroBallCompactClass_isIso 1 (by norm_num) 3
  let := integralHomologyZeroAugmentation_isIso E
  have hi : IsIso (ModuleCat.ofHom ev.toLinearMap) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ev.bijective
  have hi' : IsIso (integralCompactSupportCohomologyClass K 3 ≫
      integralCompactSupportCapThree hD omega hlocal ≫ integralHomologyZeroAugmentation E) :=
    hcomp.symm ▸ hi
  let := hi'
  have hright : IsIso (integralCompactSupportCapThree hD omega hlocal ≫
      integralHomologyZeroAugmentation E) :=
    IsIso.of_isIso_comp_left (integralCompactSupportCohomologyClass K 3) _
  let := hright
  exact IsIso.of_isIso_comp_right (integralCompactSupportCapThree hD omega hlocal)
    (integralHomologyZeroAugmentation E)

end Poincare.Topology
