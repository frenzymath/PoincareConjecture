import PoincareConjecture.Statements.M59LoopIdentification
import PoincareConjecture.Definitions.M58LoopSmoothing

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

noncomputable def m59ConstantFamily
    (q : M59SphereQuotient) (x : M) : FreeTwoSphereFamily (M := M) := by
  let F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)) :=
    constantLoopFamily x
  let R : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M)) :=
    ContinuousMap.const _ (constantC1Loop x)
  let E : LoopTwoSphere × LoopPlane → M := fun _ => x
  refine {
    basepoint := x
    family := F
    homotopy_class := 1
    class_certificate := {
      cube_representative := R
      boundary_const := by intro y hy; rfl
      sphere_parameter := q.map
      sphere_parameter_surjective := q.surjective
      sphere_parameter_boundary_collapsed := ⟨q.pole, q.boundary_collapsed⟩
      sphere_parameter_quotient_fiber := q.exact_fibers
      family_agreement := by intro y; rfl
      class_eq := by
        rfl }
    continuous := F.continuous
    derivative_continuous := by
      intro i
      change Continuous (fun p : LoopTwoSphere × LoopCircle =>
        c1LoopDerivative (constantC1Loop x) p.2 i)
      convert (continuous_const : Continuous (fun _ : LoopTwoSphere × LoopCircle =>
        (⟨x, 0⟩ : TangentBundle (𝓡 3) M))) using 1
      funext p
      simp only [c1LoopDerivative]
      congr 1
      rw [show c1LoopExtension (constantC1Loop x) = (fun _ : LoopPlane => x) by rfl]
      rw [mfderiv_const]
      rfl
    null_homotopic := by
      intro c
      refine ⟨fun _ => x, continuous_const, ?_⟩
      intro z
      rfl
    joint_extension := by
      refine ⟨E, ?_, ?_, ?_⟩
      · exact continuous_const.continuousOn
      · intro c z
        rfl
      · intro c
        simpa using (contMDiff_const.contMDiffOn :
          ContMDiffOn (𝓡 2) (𝓡 3) 1 (fun _ : LoopPlane => x) loopAnnulus) }

theorem m59ConstantFamily_normalized
    (q : M59SphereQuotient) (x : M) :
    M59NormalizedAt q x (m59ConstantFamily q x) := by
  refine ⟨rfl, ?_⟩
  rfl

theorem m59ConstantFamily_class
    (q : M59SphereQuotient) (x : M) :
    familySigmaClass (m59ConstantFamily q x) =
      ⟨x, (1 : HomotopyGroup.Pi 2
        (C1FreeLoopSpace (M := M)) (constantC1Loop x))⟩ := by
  rfl

theorem m67_raw_nontrivial_of_normalized_family
    (S : M59IdentificationSystem.{u})
    [T2Space M] [SecondCountableTopology M]
    (compact : IsCompact (Set.univ : Set M))
    (connected : IsConnected (Set.univ : Set M))
    (x : M)
    (pi_two : Subsingleton (HomotopyGroup.Pi 2 M x))
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x))
    (Gamma : FreeTwoSphereFamily (M := M))
    (hnormalized : M59NormalizedAt S.quotient x Gamma)
    (hclass : familySigmaClass Gamma = ⟨x, alpha⟩)
    (halpha : alpha ≠ 1) :
    ¬ (m59FamilyMap Gamma).Homotopic (constantLoopFamily x) := by
  intro hconst
  let C := S.core compact connected x pi_two
  have hzero := m59ConstantFamily_normalized S.quotient x
  have hzero_class := m59ConstantFamily_class S.quotient x
  have hhom : (m59FamilyMap Gamma).Homotopic
      (m59FamilyMap (m59ConstantFamily S.quotient x)) := by
    exact hconst.trans (ContinuousMap.Homotopic.refl (constantLoopFamily x))
  have hsigma : familySigmaClass Gamma =
      familySigmaClass (m59ConstantFamily S.quotient x) :=
    (C.free_class_identification Gamma (m59ConstantFamily S.quotient x)
      hnormalized hzero).mp hhom
  have hpair : (⟨x, alpha⟩ : Sigma (fun z : M =>
      HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop z))) =
      ⟨x, (1 : HomotopyGroup.Pi 2
        (C1FreeLoopSpace (M := M)) (constantC1Loop x))⟩ := by
    exact hclass.symm.trans (hsigma.trans hzero_class)
  apply halpha
  exact eq_of_heq (Sigma.mk.inj hpair).2

end PoincareConjecture
