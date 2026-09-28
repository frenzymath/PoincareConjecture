import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.CompactRepresentatives
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hs : SmoothOverlap U hU O)

theorem eventually_tensor_error_lt_on_compact_quotient
    [T2Space (Quotient O.setoid)]
    (g : ∀ i, ℝ → CanonicalMetric U hU i)
    (hg : ∀ t, CompatibleMetrics U hU O (fun i => g i t))
    {J : Set ℝ} :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hs
    letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
      fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
    (∀ i, ContinuousOn (Y := EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun p : ℝ × Piece U i => ((g i p.1).inner p.2 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (J ×ˢ univ)) →
    ∀ A : ℕ → ℝ → (x : Quotient O.setoid) → TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] ℝ,
    (∀ i I C, IsCompact I → I ⊆ J → IsCompact C → TendstoUniformlyOn
      (fun k (p : ℝ × Piece U i) =>
        let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
          A k p.1 (O.include i p.2)
        let D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
          mfderiv (𝓡 n) (𝓡 n) (O.include i) p.2
        B.bilinearComp D D)
      (fun p => (g i p.1).inner p.2) atTop (I ×ˢ C)) →
    ∀ K I, IsCompact K → IsCompact I → I ⊆ J → ∀ ε > 0,
      ∀ᶠ k in atTop, ∀ t ∈ I, ∀ x ∈ K, ∀ v w : TangentSpace (𝓡 n) x,
        Real.sqrt ((quotientMetric U hU O hs (fun i => g i t) (hg t)).inner x v v) ≤ 1 →
        Real.sqrt ((quotientMetric U hU O hs (fun i => g i t) (hg t)).inner x w w) ≤ 1 →
        |A k t x v w -
          (quotientMetric U hU O hs (fun i => g i t) (hg t)).inner x v w| < ε := by
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hs
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  intro hcont A hconv K I hK hI hIJ ε hε
  classical
  obtain ⟨s, C, hC, hcover⟩ := exists_finite_compact_representatives O hK hK.isClosed
  have hlocal (a : Σ i, Piece U i) (ha : a ∈ s) :
      ∀ᶠ k in atTop, ∀ p ∈ I ×ˢ C a, ∀ v w : EuclideanSpace ℝ (Fin n),
        (g a.1 p.1).inner p.2 v v ≤ 1 → (g a.1 p.1).inner p.2 w w ≤ 1 →
        |A k p.1 (O.include a.1 p.2)
            (mfderiv (𝓡 n) (𝓡 n) (O.include a.1) p.2 v)
            (mfderiv (𝓡 n) (𝓡 n) (O.include a.1) p.2 w) -
          (g a.1 p.1).inner p.2 v w| < ε := by
    apply eventually_bilinear_error_lt_on_unit_sublevels (hI.prod (hC a ha))
      ((hcont a.1).mono (prod_mono hIJ (subset_univ _)))
      (fun p _ v hv => (g a.1 p.1).pos p.2 v hv)
      (hconv a.1 I (C a) hI hIJ (hC a ha)) hε
  filter_upwards [s.eventually_all.mpr hlocal] with k hk t ht x hx v w hv hw
  rw [← hcover] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ := by
    simpa only [mem_iUnion, exists_prop, mem_image] using hx
  let L := (include_isLocalDiffeomorph U hU O hs a.1).mfderivToContinuousLinearEquiv
    (by simp) y
  obtain ⟨v', hv'⟩ := L.surjective v
  obtain ⟨w', hw'⟩ := L.surjective w
  change mfderiv (𝓡 n) (𝓡 n) (O.include a.1) y v' = v at hv'
  change mfderiv (𝓡 n) (𝓡 n) (O.include a.1) y w' = w at hw'
  subst v w
  have hpull := quotientMetric_preserves U hU O hs (fun i => g i t) (hg t) a.1 y
  have hvv : (g a.1 t).inner y v' v' ≤ 1 := by
    rw [← hpull v' v'] at hv
    exact Real.sqrt_le_one.mp hv
  have hww : (g a.1 t).inner y w' w' ≤ 1 := by
    rw [← hpull w' w'] at hw
    exact Real.sqrt_le_one.mp hw
  simpa only [ContinuousLinearMap.bilinearComp_apply, ← hpull v' w'] using
    hk a ha (t, y) ⟨ht, hy⟩ v' w' hvv hww

end PoincareConjecture.ChartDistance
