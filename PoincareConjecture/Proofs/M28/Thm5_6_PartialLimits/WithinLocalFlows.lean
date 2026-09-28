import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinBilinearFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.LocalFlows












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance




theorem exists_ricciFlow_on_within_coordinate_limit
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (Fseq : ∀ k, RicciFlow n (M k) J)
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
      (fun k => iteratedFDerivWithin ℝ m (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq k).metric p.1).pullbackCoefficients (chartParametrization U hU (e k)) p.2)
        (J ×ˢ U i))
      (iteratedFDerivWithin ℝ m B (J ×ˢ U i)) atTop K) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∃ F : RicciFlow n (Piece U i) J, F.metric = g := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let Fchart : ℕ → RicciFlow n (Piece U i) J := fun k =>
    (Fseq k).pullbackToCanonicalDomain (U i) (hU i) (e k) (he k)
  apply RicciFlow.exists_of_bilinear_within_spacetime_jets Fchart g hJ hg
  intro x m K hK hKU
  rw [canonical_extChartAt_target U hU] at hKU ⊢
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
    ((hseq k).iteratedFDerivWithin m).mono hKU)).congr_right
      ((hlim.iteratedFDerivWithin m).mono hKU)

end PoincareConjecture.ChartDistance
