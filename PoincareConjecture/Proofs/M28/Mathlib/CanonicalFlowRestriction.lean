import PoincareConjecture.Proofs.M28.Mathlib.CanonicalDomainInclusion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M28

variable {n : ℕ} {J : Set ℝ}
  {U V : Set (EuclideanSpace ℝ (Fin n))}
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
  [Nonempty U] [Nonempty V]

def canonicalFlowRestriction :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    RicciFlow n V J →
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    RicciFlow n U J := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro F
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  exact F.pullbackToCanonicalDomain U hU
    (fun x => ⟨x.val, hUV x.property⟩)
    (Poincare.isLocalDiffeomorph_canonicalDomainInclusion (𝕜 := ℝ) hU hV hUV)

theorem canonicalFlowRestriction_inner :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ F : RicciFlow n V J,
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (t : ℝ) (x : U) (v w : EuclideanSpace ℝ (Fin n)),
      ((canonicalFlowRestriction hU hV hUV F).metric t).inner x v w =
        (F.metric t).inner ⟨x.val, hUV x.property⟩ v w := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro F
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro t x v w
  let j : U → V := fun y => ⟨y.val, hUV y.property⟩
  change (F.metric t).inner (j x) (mfderiv (𝓡 n) (𝓡 n) j x v)
    (mfderiv (𝓡 n) (𝓡 n) j x w) = (F.metric t).inner (j x) v w
  rw [Poincare.mfderiv_canonicalDomainInclusion (𝕜 := ℝ) hU hV hUV x]
  rfl

theorem canonicalFlowRestriction_scalar :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ F : RicciFlow n V J,
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (t : ℝ) (x : U),
      ((canonicalFlowRestriction hU hV hUV F).connection t).scalarCurvature x =
        (F.connection t).scalarCurvature ⟨x.val, hUV x.property⟩ := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro F
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro t x
  let j : U → V := fun y => ⟨y.val, hUV y.property⟩
  have hj := Poincare.isLocalDiffeomorph_canonicalDomainInclusion (𝕜 := ℝ) hU hV hUV
  let D := (canonicalFlowRestriction hU hV hUV F).connection t
  exact D.scalarCurvature_eq_of_local_isometry (F.connection t)
    isOpen_univ hj.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem canonicalFlowRestriction_nonnegative_iff :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ F : RicciFlow n V J,
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (t : ℝ) (x : U),
      ((canonicalFlowRestriction hU hV hUV F).connection t).NonnegativeCurvatureOperator x ↔
        (F.connection t).NonnegativeCurvatureOperator ⟨x.val, hUV x.property⟩ := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro F
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro t x
  have hj := Poincare.isLocalDiffeomorph_canonicalDomainInclusion (𝕜 := ℝ) hU hV hUV
  let D := (canonicalFlowRestriction hU hV hUV F).connection t
  exact D.nonnegativeCurvatureOperator_iff_of_local_isometry (F.connection t)
    isOpen_univ hj.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)

end PoincareConjecture.M28
