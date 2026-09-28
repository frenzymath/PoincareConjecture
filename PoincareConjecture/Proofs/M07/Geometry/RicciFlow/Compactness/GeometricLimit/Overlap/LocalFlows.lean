import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CanonicalDomain
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.BilinearJets
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]

theorem canonical_extChartAt_target (i : ι) (p : Piece U i) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    (extChartAt (𝓡 n) p).target = U i := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  rw [extChartAt_target, ModelWithCorners.range_eq_univ, inter_univ]
  simp only [modelWithCornersSelf_coe_symm, preimage_id]
  change ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph).target = U i
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact Subtype.range_val

theorem canonical_pullbackMetric_coefficients
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n N) {i : ι} (e : Piece U i → N)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e) (p x : Piece U i) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    (g.pullbackOfLocalDiffeomorph e he).pullbackCoefficients
      (extChartAt (𝓡 n) p).symm (x : EuclideanSpace ℝ (Fin n)) =
      g.pullbackCoefficients (chartParametrization U hU e) x := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  rw [RiemannianMetric.pullbackCoefficients_canonicalChart (U i) (hU i)]
  have hd := mfderiv_chartParametrization U hU x (he.contMDiff x)
  ext v w
  change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) =
    g.inner (chartParametrization U hU e x)
      (mfderiv (𝓡 n) (𝓡 n) (chartParametrization U hU e) x v)
      (mfderiv (𝓡 n) (𝓡 n) (chartParametrization U hU e) x w)
  rw [chartParametrization_apply, hd]
  rfl

theorem exists_ricciFlow_on_coordinate_limit
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} (hJ : IsOpen J) (Fseq : ∀ k, RicciFlow n (M k) J)
    (i : ι) (e : ∀ k, Piece U i → M k)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (g : ℝ → CanonicalMetric U hU i)
    (hg : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      RiemannianMetric.IsSmoothFamilyOn g J)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hcoeff : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ t ∈ J, ∀ (x : Piece U i) v w, (g t).inner x v w = B (t, x) v w)
    (hjet : ∀ m K, IsCompact K → K ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq k).metric p.1).pullbackCoefficients (chartParametrization U hU (e k)) p.2))
      (iteratedFDeriv ℝ m B) atTop K) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∃ F : RicciFlow n (Piece U i) J, F.metric = g := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let Fchart : ℕ → RicciFlow n (Piece U i) J := fun k =>
    (Fseq k).pullbackToCanonicalDomain (U i) (hU i) (e k) (he k)
  apply RicciFlow.exists_of_bilinear_spacetime_jets Fchart g hJ hg
  intro x m K hK hKU
  rw [canonical_extChartAt_target U hU] at hKU
  have hseq (k : ℕ) : EqOn
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq k).metric p.1).pullbackCoefficients (chartParametrization U hU (e k)) p.2)
      (fun p => ((Fchart k).metric p.1).pullbackCoefficients
        (extChartAt (𝓡 n) x).symm p.2) (J ×ˢ U i) := by
    intro p hp
    exact (canonical_pullbackMetric_coefficients U hU ((Fseq k).metric p.1)
      (e k) (he k) x ⟨p.2, hp.2⟩).symm
  have hlim : EqOn B (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2) (J ×ˢ U i) := by
    intro p hp
    have hform : B p = (g p.1).inner ⟨p.2, hp.2⟩ := by
      ext v w
      exact (hcoeff p.1 hp.1 ⟨p.2, hp.2⟩ v w).symm
    exact hform.trans (RiemannianMetric.pullbackCoefficients_canonicalChart (U i) (hU i)
      (g p.1) x ⟨p.2, hp.2⟩).symm
  exact ((hjet m K hK hKU).congr (Eventually.of_forall fun k =>
    (eqOn_iteratedFDeriv_of_isOpen (hJ.prod (hU i)) (hseq k) m).mono hKU)).congr_right
      ((eqOn_iteratedFDeriv_of_isOpen (hJ.prod (hU i)) hlim m).mono hKU)

end PoincareConjecture.ChartDistance
