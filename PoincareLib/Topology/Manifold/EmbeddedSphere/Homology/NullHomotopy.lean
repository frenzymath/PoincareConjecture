import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic
import PoincareLib.Topology.Manifold.EmbeddedSphere.Homology.NullMap

/-!
# The null-homology input for sphere separation

We package the primitive sphere map in the ambient universe, preserve its
free null-homotopy, and prove that it induces zero in positive-degree homology.
This supplies the homotopy-invariance step of the repair used in Morgan--Tian
Proposition 15.12 and Remark 15.13, printed p. 365. The homology argument is
Hatcher, Proposition 2.8 and Theorem 2.10, pp. 110-111; see derivation 01 in
`proof-work/tasks/M53/derivations/`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

universe u v w

namespace PoincareMT.Topology.EmbeddedSphere

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The sphere as a continuous map in the ambient universe. The universe lift
does not change its topology or image; this packages the input to the
separation repair for Morgan--Tian Proposition 15.12, printed p. 365. -/
def sphereContinuousMap (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    C(ULift.{u} UnitTwoSphere, M) :=
  ⟨fun x => S.sphere x.down,
    S.smooth_embedding.isEmbedding.continuous.comp continuous_uliftDown⟩

/-- The free null-homotopy in the frozen interface survives the universe lift.
Source: M53 definition and derivation 01, for Morgan--Tian p. 365. -/
theorem sphereContinuousMap_nullHomotopic
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    ∃ y : M, (sphereContinuousMap S).Homotopic (ContinuousMap.const _ y) := by
  obtain ⟨hcontinuous, y, ⟨H⟩⟩ := S.null_homotopic
  exact ⟨y, ⟨H.compContinuousMap ⟨ULift.down, continuous_uliftDown⟩⟩⟩

/-- A null-homotopic embedded sphere induces zero in every positive homology
degree, for arbitrary coefficients. Hatcher, pp. 110-111; separation repair
for Morgan--Tian Proposition 15.12 and Remark 15.13, printed p. 365. -/
theorem sphereContinuousMap_homologyMap_eq_zero
    {C : Type v} [Category.{w} C] [Preadditive C] [Limits.HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C)
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) (n : Nat) (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map
      (TopCat.ofHom (sphereContinuousMap S)) = 0 := by
  obtain ⟨y, ⟨H⟩⟩ := sphereContinuousMap_nullHomotopic S
  exact TopCat.Homotopy.singularHomologyMap_eq_zero_of_const
    (f := TopCat.ofHom (sphereContinuousMap S)) (y := y) H R n hn

/-- The inclusion of the actual sphere range is freely null-homotopic.
This transports the given sphere homotopy through the embedding's inverse,
as needed for the relative homology sequence of the pair. Source: M53
derivations 01-02, for Morgan--Tian Proposition 15.12, printed p. 365. -/
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

/-- The inclusion of the sphere range induces zero in positive-degree
homology, so its degree-two classes can enter the relative exact sequence.
Source: Hatcher pp. 110-111 and M53 derivations 01-02, for Morgan--Tian p. 365. -/
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

/-- A smoothly embedded two-sphere has closed range in a Hausdorff target,
since its domain is compact. This is the closed-subspace input for the
separation repair of Morgan--Tian Proposition 15.12, printed p. 365. -/
theorem sphere_isClosedEmbedding [T2Space M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    Topology.IsClosedEmbedding S.sphere :=
  S.smooth_embedding.isEmbedding.continuous.isClosedEmbedding
    S.smooth_embedding.isEmbedding.injective

/-- The complement of the sphere is open. Source: the compact embedding
argument in derivation 01, for Morgan--Tian Proposition 15.12, p. 365. -/
theorem sphere_isOpen_compl [T2Space M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    IsOpen (Set.univ \ Set.range S.sphere) :=
  isOpen_univ.sdiff (sphere_isClosedEmbedding S).isClosed_range

end PoincareMT.Topology.EmbeddedSphere
