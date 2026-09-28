import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceDensity
import PoincareConjecture.Proofs.M34.Standard.CanonicalPullbackTensors
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

noncomputable def canonicalCoreFlow {n : ℕ} {J : Set ℝ} (F : RicciFlow n (V n) J) :
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 n) (n := ∞)
    RicciFlow n (univ : Set (V n)) J :=
  F.pullbackToCanonicalDomain univ isOpen_univ Subtype.val
    (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) univ isOpen_univ ∞)

theorem canonicalCoreFlow_inner {n : ℕ} {J : Set ℝ} (F : RicciFlow n (V n) J) :
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 n) (n := ∞)
    ∀ (t : ℝ) (x : (univ : Set (V n))),
      ((canonicalCoreFlow F).metric t).inner x = (F.metric t).inner (x : V n) := by
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 n) (n := ∞)
  intro t x
  ext u v
  change (F.metric t).inner (x : V n)
    (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : ↑(univ : Set (V n)) → V n) x u)
    (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : ↑(univ : Set (V n)) → V n) x v) = _
  erw [mfderiv_subtypeVal_singleton isOpen_univ x]
  rfl

theorem canonicalCoreFlow_density {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {J J' : Set ℝ} (F : RicciFlow n (V n) J) (F' : RicciFlow n (V n) J') :
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 n) (n := ∞)
    ∀ (t : ℝ) (x : (univ : Set (V n))),
      actualDifferenceEnergyDensity qH qA qS
        ((canonicalCoreFlow F).connection t) ((canonicalCoreFlow F').connection t) x =
      actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t) (x : V n) := by
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 n) (n := ∞)
  intro t x
  let hf := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) (univ : Set (V n)) isOpen_univ ∞
  have hA : CovariantDerivative.difference ((canonicalCoreFlow F).connection t).connection
      ((canonicalCoreFlow F').connection t).connection x =
      CovariantDerivative.difference (F.connection t).connection (F'.connection t).connection
        (x : V n) := by
    ext u v
    have hh := canonicalDomain_pullback_connection_difference univ isOpen_univ Subtype.val hf
      F F' t x u v
    erw [mfderiv_subtypeVal_singleton isOpen_univ x, ContinuousLinearMap.inverse_id] at hh
    exact hh
  have hR {I : Set ℝ} (G : RicciFlow n (V n) I) :
      curvatureTrilinearMap ((canonicalCoreFlow G).connection t) x =
        curvatureTrilinearMap (G.connection t) (x : V n) := by
    ext u v w
    have hh := canonicalDomain_pullback_curvature univ isOpen_univ Subtype.val hf G t x u v w
    erw [mfderiv_subtypeVal_singleton isOpen_univ x, ContinuousLinearMap.inverse_id] at hh
    exact (curvatureTrilinearMap_apply ((canonicalCoreFlow G).connection t) x u v w).trans
      (hh.trans (curvatureTrilinearMap_apply (G.connection t) (x : V n) u v w).symm)
  dsimp only [actualDifferenceEnergyDensity]
  rw [canonicalCoreFlow_inner F t x, canonicalCoreFlow_inner F' t x, hA, hR F, hR F']

theorem canonicalCoreFlow_chart_density {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {J J' : Set ℝ} (F : RicciFlow n (V n) J) (F' : RicciFlow n (V n) J') :
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 n) (n := ∞)
    ∀ (p : (univ : Set (V n))) (t : ℝ) (x : V n),
      canonicalDifferenceDensity univ isOpen_univ qH qA qS
        (canonicalCoreFlow F) (canonicalCoreFlow F') p t x =
        actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t) x := by
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 n) (n := ∞)
  intro p t x
  exact (canonicalDifferenceDensity_coe univ isOpen_univ qH qA qS
    (canonicalCoreFlow F) (canonicalCoreFlow F') p t ⟨x, mem_univ x⟩).trans
      (canonicalCoreFlow_density qH qA qS F F' t ⟨x, mem_univ x⟩)

theorem actualDifferenceEnergyDensity_continuous_euclidean {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {J J' : Set ℝ} (F : RicciFlow n (V n) J) (F' : RicciFlow n (V n) J')
    {t : ℝ} (ht : t ∈ J ∩ J') :
    Continuous (actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t)) := by
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 n) (n := ∞)
  let p : (univ : Set (V n)) := ⟨0, mem_univ 0⟩
  have hc := continuousOn_univ.mp (canonicalDifferenceDensity_continuousOn_slice univ isOpen_univ
    qH qA qS (canonicalCoreFlow F) (canonicalCoreFlow F') p ht)
  have heq := funext (canonicalCoreFlow_chart_density qH qA qS F F' p t)
  rwa [heq] at hc

end PoincareConjecture.M34
