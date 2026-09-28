import PoincareConjecture.Definitions.M53SphereSeparation
import PoincareConjecture.Proofs.M53.Mathlib.NullHomotopicHomology

set_option autoImplicit false

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

universe u v w

namespace PoincareConjecture.Proofs.M53

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

def sphereContinuousMap (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    C(ULift.{u} UnitTwoSphere, M) :=
  ⟨fun x => S.sphere x.down,
    S.smooth_embedding.isEmbedding.continuous.comp continuous_uliftDown⟩

theorem sphereContinuousMap_nullHomotopic
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    ∃ y : M, (sphereContinuousMap S).Homotopic (ContinuousMap.const _ y) := by
  obtain ⟨hcontinuous, y, ⟨H⟩⟩ := S.null_homotopic
  exact ⟨y, ⟨H.compContinuousMap ⟨ULift.down, continuous_uliftDown⟩⟩⟩

theorem sphereContinuousMap_homologyMap_eq_zero
    {C : Type v} [Category.{w} C] [Preadditive C] [Limits.HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C)
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) (n : Nat) (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map
      (TopCat.ofHom (sphereContinuousMap S)) = 0 := by
  obtain ⟨y, ⟨H⟩⟩ := sphereContinuousMap_nullHomotopic S
  exact TopCat.Homotopy.singularHomologyMap_eq_zero_of_const
    (f := TopCat.ofHom (sphereContinuousMap S)) (y := y) H R n hn

theorem sphereRangeInclusion_nullHomotopic
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    ∃ y : M, ContinuousMap.Homotopic
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range S.sphere, M))
      (ContinuousMap.const _ y) := by
  classical
  obtain ⟨y, ⟨H⟩⟩ := sphereContinuousMap_nullHomotopic S
  let e := S.smooth_embedding.isEmbedding.toHomeomorph
  let r : C(Set.range S.sphere, ULift.{u} UnitTwoSphere) :=
    ⟨fun x => ULift.up (e.symm x), continuous_uliftUp.comp e.symm.continuous⟩
  have hcomp : (sphereContinuousMap S).comp r =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range S.sphere, M)) := by
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨y, ?_⟩
  rw [← hcomp]
  exact ⟨H.compContinuousMap r⟩

theorem sphereRangeInclusion_homologyMap_eq_zero
    {C : Type v} [Category.{w} C] [Preadditive C] [Limits.HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C)
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) (n : Nat) (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range S.sphere, M))) =
        0 := by
  obtain ⟨y, ⟨H⟩⟩ := sphereRangeInclusion_nullHomotopic S
  exact TopCat.Homotopy.singularHomologyMap_eq_zero_of_const
    (f := TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range S.sphere, M)))
    (y := y) H R n hn

theorem sphere_isClosedEmbedding [T2Space M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    Topology.IsClosedEmbedding S.sphere :=
  S.smooth_embedding.isEmbedding.continuous.isClosedEmbedding
    S.smooth_embedding.isEmbedding.injective

theorem sphere_isOpen_compl [T2Space M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    IsOpen (Set.univ \ Set.range S.sphere) :=
  isOpen_univ.sdiff (sphere_isClosedEmbedding S).isClosed_range

end PoincareConjecture.Proofs.M53
