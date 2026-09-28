import PoincareConjecture.Proofs.M47.TerminalGermsInteriorFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.LocalFlows











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47



theorem terminalGerms_exists_closed_chart_flow
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {a : ℝ} (ha : a < 0) (Fseq : ∀ k, RicciFlow n (M k) (Icc a 0))
    (i : ι) (e : ∀ k, Piece U i → M k)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (g : ℝ → CanonicalMetric U hU i)
    (hg : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      RiemannianMetric.IsSmoothFamilyOn g (Icc a 0))
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hcoeff : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ t ∈ Icc a 0, ∀ (x : Piece U i) v w, (g t).inner x v w = B (t, x) v w)
    (hjet : ∀ m K, IsCompact K → K ⊆ Ioo a 0 ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq k).metric p.1).pullbackCoefficients
          (ChartDistance.chartParametrization U hU (e k)) p.2))
      (iteratedFDeriv ℝ m B) atTop K) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∃ F : RicciFlow n (Piece U i) (Icc a 0), F.metric = g := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  have hnontrivial : (Ioo a 0).Nontrivial := by
    obtain ⟨x, hax, hx⟩ := exists_between ha
    obtain ⟨y, hxy, hy⟩ := exists_between hx
    exact ⟨x, ⟨hax, hx⟩, y, ⟨hax.trans hxy, hy⟩, hxy.ne⟩
  let Fopen : ∀ k, RicciFlow n (M k) (Ioo a 0) := fun k => {
    metric := (Fseq k).metric
    connection := (Fseq k).connection
    interval := ordConnected_Ioo
    nontrivial := hnontrivial
    smooth := (Fseq k).smooth.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
    equation := fun t ht x v w =>
      ((Fseq k).equation t (Ioo_subset_Icc_self ht) x v w).mono Ioo_subset_Icc_self }
  obtain ⟨Fminus, hmetric⟩ := ChartDistance.exists_ricciFlow_on_coordinate_limit U hU
    isOpen_Ioo Fopen i e he g
    (hg.mono (prod_mono Ioo_subset_Icc_self subset_rfl)) B
    (fun t ht => hcoeff t (Ioo_subset_Icc_self ht)) hjet
  subst g
  apply terminalGerms_exists_flow_of_interior Fminus.metric Fminus.connection hg
    ordConnected_Icc
    (show (Icc a 0).Nontrivial from
      ⟨a, ⟨le_rfl, ha.le⟩, 0, ⟨ha.le, le_rfl⟩, ha.ne⟩)
  intro t ht x v w
  have ht' : t ∈ Ioo a 0 := by simpa only [interior_Icc] using ht
  exact (Fminus.equation t ht' x v w).hasDerivAt (isOpen_Ioo.mem_nhds ht')

end PoincareConjecture.M47
