import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]

private theorem mfderiv_canonicalSubtypeInverse (i : ι) (x : Piece U i) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    mfderiv (𝓡 n) (𝓡 n)
      (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm
      (x : EuclideanSpace ℝ (Fin n)) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  have hc : ⇑(extChartAt (𝓡 n) x) =
      (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) := rfl
  have hi : ⇑(extChartAt (𝓡 n) x).symm =
      (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm := rfl
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ, hc, hi] at hd
  exact hd

theorem mfderiv_chartParametrization
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {i : ι} {e : Piece U i → M} (x : Piece U i)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    mfderiv (𝓡 n) (𝓡 n) (chartParametrization U hU e)
      (x : EuclideanSpace ℝ (Fin n)) = mfderiv (𝓡 n) (𝓡 n) e x := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let r := (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm
  have hr : r (x : EuclideanSpace ℝ (Fin n)) = x :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n))
      (hU i).isOpenEmbedding_subtypeVal
  have hrs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ r (x : EuclideanSpace ℝ (Fin n)) :=
    (contMDiffOn_isOpenEmbedding_symm (I := 𝓡 n) (n := ∞)
      (hU i).isOpenEmbedding_subtypeVal).contMDiffAt
      ((hU i).isOpenEmbedding_subtypeVal.isOpen_range.mem_nhds ⟨x, rfl⟩)
  have he' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (r (x : EuclideanSpace ℝ (Fin n))) := by
    rw [hr]
    exact he
  have hd := mfderiv_comp (x : EuclideanSpace ℝ (Fin n))
    (he'.mdifferentiableAt (by simp)) (hrs.mdifferentiableAt (by simp))
  have hdr : mfderiv (𝓡 n) (𝓡 n) r (x : EuclideanSpace ℝ (Fin n)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    mfderiv_canonicalSubtypeInverse U hU i x
  rw [hr, hdr] at hd
  ext v
  exact congrArg (fun A => A v) hd

variable (O : OverlapSystem (fun i => Piece U i)) (hs : SmoothOverlap U hU O)
    (g : ∀ i, CanonicalMetric U hU i) (hg : CompatibleMetrics U hU O g)

theorem quotientMetric_pullbackCoefficients (i : ι) (x : Piece U i) :
    letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U j) :=
      fun j => (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ j, IsManifold (𝓡 n) ∞ (Piece U j) :=
      fun j => (hU j).isOpenEmbedding_subtypeVal.isManifold_singleton
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hs
    (quotientMetric U hU O hs g hg).pullbackCoefficients
      (chartParametrization U hU (O.include i)) (x : EuclideanSpace ℝ (Fin n)) =
        (g i).inner x := by
  let : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U j) :=
    fun j => (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ j, IsManifold (𝓡 n) ∞ (Piece U j) :=
    fun j => (hU j).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hs
  have hd := mfderiv_chartParametrization U hU x
    ((include_isLocalDiffeomorph U hU O hs i).contMDiff x)
  ext v w
  change (quotientMetric U hU O hs g hg).inner
    (chartParametrization U hU (O.include i) x)
    (mfderiv (𝓡 n) (𝓡 n) (chartParametrization U hU (O.include i)) x v)
    (mfderiv (𝓡 n) (𝓡 n) (chartParametrization U hU (O.include i)) x w) =
      (g i).inner x v w
  rw [chartParametrization_apply, hd]
  exact (quotientMetric_preserves U hU O hs g hg i x v w).symm

theorem quotientMetric_pullbackCoefficients_eqOn
    (B : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U j) :=
        fun j => (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ j, IsManifold (𝓡 n) ∞ (Piece U j) :=
        fun j => (hU j).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ j (x : Piece U j) v w, (g j).inner x v w = B j x v w)
    (i : ι) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hs
    EqOn ((quotientMetric U hU O hs g hg).pullbackCoefficients
      (chartParametrization U hU (O.include i))) (B i) (U i) := by
  let : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U j) :=
    fun j => (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ j, IsManifold (𝓡 n) ∞ (Piece U j) :=
    fun j => (hU j).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hs
  intro x hx
  rw [quotientMetric_pullbackCoefficients U hU O hs g hg i ⟨x, hx⟩]
  ext v w
  exact hB i ⟨x, hx⟩ v w

theorem quotientMetric_family_pullbackCoefficients_eqOn
    (gFamily : ∀ i, ℝ → CanonicalMetric U hU i)
    (hcompat : ∀ t, CompatibleMetrics U hU O (fun i => gFamily i t))
    {J : Set ℝ}
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U j) :=
        fun j => (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ j, IsManifold (𝓡 n) ∞ (Piece U j) :=
        fun j => (hU j).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ t ∈ J, ∀ j (x : Piece U j) v w, (gFamily j t).inner x v w = B j (t, x) v w)
    (i : ι) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hs
    EqOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (quotientMetric U hU O hs (fun j => gFamily j p.1) (hcompat p.1)).pullbackCoefficients
        (chartParametrization U hU (O.include i)) p.2) (B i) (J ×ˢ U i) := by
  let : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U j) :=
    fun j => (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ j, IsManifold (𝓡 n) ∞ (Piece U j) :=
    fun j => (hU j).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hs
  intro p hp
  exact quotientMetric_pullbackCoefficients_eqOn U hU O hs
    (fun j => gFamily j p.1) (hcompat p.1) (fun j x => B j (p.1, x))
    (hB p.1 hp.1) i hp.2

end PoincareConjecture.ChartDistance
