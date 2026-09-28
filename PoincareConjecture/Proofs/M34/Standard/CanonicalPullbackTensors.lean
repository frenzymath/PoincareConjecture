import PoincareConjecture.Proofs.M34.Standard.CanonicalPullbackCoefficients
import PoincareConjecture.Proofs.M34.Standard.LocalIsometryDifferences











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {n : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U]
  (f : U → N)
  (hf : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)

include hf

omit [IsManifold (𝓡 n) ∞ N] in


theorem canonicalDomain_pullback_mfderiv_isInvertible :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ x : U, (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro x
  exact ⟨(hf x).mfderivToContinuousLinearEquiv (by simp), rfl⟩



theorem canonicalDomain_pullback_connection_difference :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n N J) (F' : RicciFlow n N J')
      (t : ℝ) (x : U) (u v : TangentSpace (𝓡 n) x),
      CovariantDerivative.difference
        ((F.pullbackToCanonicalDomain U hU f hf).connection t).connection
        ((F'.pullbackToCanonicalDomain U hU f hf).connection t).connection x u v =
        (mfderiv (𝓡 n) (𝓡 n) f x).inverse
          (CovariantDerivative.difference (F.connection t).connection (F'.connection t).connection
            (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' t x u v
  exact LeviCivitaData.connection_difference_eq_of_local_isometries
    ((F.pullbackToCanonicalDomain U hU f hf).connection t)
    ((F'.pullbackToCanonicalDomain U hU f hf).connection t)
    (F.connection t) (F'.connection t) (hf.contMDiff x)
    (Eventually.of_forall (canonicalDomain_pullback_mfderiv_isInvertible U hU f hf))
    (Eventually.of_forall (fun _ _ _ => rfl)) (Eventually.of_forall (fun _ _ _ => rfl)) u v




theorem canonicalDomain_pullback_curvature :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J : Set ℝ} (F : RicciFlow n N J) (t : ℝ) (x : U)
      (u v w : TangentSpace (𝓡 n) x),
      ((F.pullbackToCanonicalDomain U hU f hf).connection t).curvature x u v w =
        (mfderiv (𝓡 n) (𝓡 n) f x).inverse
          ((F.connection t).curvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
            (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J F t x u v w
  exact LeviCivitaData.curvature_eq_of_local_isometry
    ((F.pullbackToCanonicalDomain U hU f hf).connection t) (F.connection t)
    isOpen_univ hf.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)
    (canonicalDomain_pullback_mfderiv_isInvertible U hU f hf x) u v w

end PoincareConjecture.M34
