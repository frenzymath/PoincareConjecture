import PoincareConjecture.Proofs.M47.TerminalCurvatureSectionalLimit
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourcePinching
import PoincareConjecture.Proofs.M47.TerminalGermsChartFlow
import PoincareConjecture.Proofs.M04.FlowRiemannRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

private noncomputable local instance pinchedOperatorDualAdd : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance pinchedOperatorDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance pinchedOperatorBilinAdd :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance pinchedOperatorBilinSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem terminalGerms_operator_on_closed_of_interior
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {a : ℝ} (ha : a < 0) (F : RicciFlow 3 M (Icc a 0))
    (hinterior : ∀ t ∈ Ioo a 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Icc a 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x := by
  intro t ht x
  apply (F.connection t).nonnegativeCurvatureOperator_of_nonnegative_sectional_three
    (F.connection t).intrinsicCurvatureTensorCalculus x
  intro v w
  have hclosure : t ∈ closure (Ioo a 0) := by
    rw [closure_Ioo ha.ne]
    exact ht
  have := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  apply ge_of_tendsto
    (((M04.contDiffOn_curvatureTensor_timeSlice F x v w v w).continuousOn t ht).mono
      Ioo_subset_Icc_self)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (F.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
    x (hinterior s hs x) v w

theorem terminalGerms_operator_of_bilinear_jets
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {a : ℝ} (ha : a < 0)
    (Fseq : ℕ → RicciFlow 3 M (Icc a 0)) (F : RicciFlow 3 M (Icc a 0))
    (hjet : ∀ (x : M) (r : ℕ) (K : Set (ℝ × E)), IsCompact K →
      K ⊆ Ioo a 0 ×ˢ (extChartAt (𝓡 3) x).target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((Fseq k).metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2))
        (iteratedFDeriv ℝ r (fun p : ℝ × E =>
          (F.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2)) atTop K)
    (hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop, ∀ t ∈ Icc a 0,
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((Fseq k).connection t).sectionalCurvature x v w) :
    ∀ t ∈ Icc a 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x := by
  have hscalar (x : M) (r : ℕ) (j b : Fin 3) (K : Set (ℝ × E))
      (hK : IsCompact K) (hKU : K ⊆ Ioo a 0 ×ˢ (extChartAt (𝓡 3) x).target) :
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((Fseq k).metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2
            (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
        (iteratedFDeriv ℝ r (fun p : ℝ × E =>
          (F.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2
            (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
        atTop K := by
    let V := Ioo a 0 ×ˢ (extChartAt (𝓡 3) x).target
    have hV : IsOpen V := isOpen_Ioo.prod (isOpen_extChartAt_target x)
    have hsmooth (G : RicciFlow 3 M (Icc a 0)) :
        ContDiffOn ℝ ∞ (fun p : ℝ × E =>
          (G.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) x).symm p.2) V := by
      intro p hp
      have hg : RiemannianMetric.IsSmoothFamilyOn G.metric (Ioo a 0) :=
        G.smooth.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
      exact (hg.contDiffAt_spacetime_pullbackCoefficients isOpen_Ioo
        ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hp.2).contMDiffAt
          (extChartAt_target_mem_nhds' hp.2)) hp.1).contDiffWithinAt
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ j))
    have h := Poincare.Analysis.Calculus.smooth_convergence_continuousLinearMap_comp
      L hV (hsmooth F) (fun p hp => ⟨V, hV, hp,
        Eventually.of_forall fun k => hsmooth (Fseq k)⟩) (hjet x)
    exact h.2 r K hK hKU
  apply terminalGerms_operator_on_closed_of_interior ha F
  intro t ht x
  have hj := RiemannianMetric.spatial_and_time_jets_of_spacetime_jets
    (fun k => (Fseq k).metric) F.metric
    (fun k => (Fseq k).smooth.mono (prod_mono Ioo_subset_Icc_self subset_rfl))
    (F.smooth.mono (prod_mono Ioo_subset_Icc_self subset_rfl)) isOpen_Ioo ht x
    (fun r _ a b => RiemannianMetric.tendsto_spacetime_jet_of_compact_uniform r
      (hscalar x r a b) ⟨ht, mem_extChartAt_target x⟩)
  apply terminalCurvature_operator_of_coordinate_jets
    (fun k => (Fseq k).connection t) (F.connection t) x hj.1
  intro eta heta
  exact (hlower eta heta).mono fun k hk => hk t (Ioo_subset_Icc_self ht)

theorem terminalGerms_operator_of_original_chart_jets
    {ι : Type*} (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace E (M k)] [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {a : ℝ} (ha : a < 0) (Fseq : ∀ k, RicciFlow 3 (M k) (Icc a 0))
    (i : ι) (e : ∀ k, Piece U i → M k)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k))
    (F : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
      RicciFlow 3 (Piece U i) (Icc a 0))
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (hcoeff : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
      ∀ t ∈ Icc a 0, ∀ (x : Piece U i) v w, (F.metric t).inner x v w = B (t, x) v w)
    (hjet : ∀ m K, IsCompact K → K ⊆ Ioo a 0 ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × E =>
        ((Fseq k).metric p.1).pullbackCoefficients
          (ChartDistance.chartParametrization U hU (e k)) p.2))
      (iteratedFDeriv ℝ m B) atTop K)
    (hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop, ∀ t ∈ Icc a 0,
      ∀ (x : M k) (v w : TangentSpace (𝓡 3) x),
        -eta ≤ ((Fseq k).connection t).sectionalCurvature x v w) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc a 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let Fchart := fun k => (Fseq k).pullbackToCanonicalDomain (U i) (hU i) (e k) (he k)
  apply terminalGerms_operator_of_bilinear_jets ha Fchart F
  · intro x m K hK hKU
    rw [ChartDistance.canonical_extChartAt_target U hU] at hKU
    have hseq (k : ℕ) : EqOn
        (fun p : ℝ × E => ((Fseq k).metric p.1).pullbackCoefficients
          (ChartDistance.chartParametrization U hU (e k)) p.2)
        (fun p : ℝ × E => ((Fchart k).metric p.1).pullbackCoefficients
          (extChartAt (𝓡 3) x).symm p.2) (Ioo a 0 ×ˢ U i) := by
      intro p hp
      exact (ChartDistance.canonical_pullbackMetric_coefficients U hU
        ((Fseq k).metric p.1) (e k) (he k) x ⟨p.2, hp.2⟩).symm
    have hlim : EqOn B (fun p : ℝ × E => (F.metric p.1).pullbackCoefficients
        (extChartAt (𝓡 3) x).symm p.2) (Ioo a 0 ×ˢ U i) := by
      intro p hp
      have hform : B p = (F.metric p.1).inner ⟨p.2, hp.2⟩ := by
        ext v w
        exact (hcoeff p.1 (Ioo_subset_Icc_self hp.1) ⟨p.2, hp.2⟩ v w).symm
      exact hform.trans (RiemannianMetric.pullbackCoefficients_canonicalChart
        (U i) (hU i) (F.metric p.1) x ⟨p.2, hp.2⟩).symm
    exact ((hjet m K hK hKU).congr (Eventually.of_forall fun k =>
      (Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
        (isOpen_Ioo.prod (hU i)) (hseq k) m).mono hKU)).congr_right
      ((Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
        (isOpen_Ioo.prod (hU i)) hlim m).mono hKU)
  · intro eta heta
    filter_upwards [hlower eta heta] with k hk t ht x v w
    rw [M36.sectionalCurvature_eq_of_local_isometry ((Fchart k).connection t)
      ((Fseq k).connection t) (f := e k) isOpen_univ (he k).contMDiff.contMDiffOn
      (fun _ _ _ _ => rfl) (mem_univ x) v w]
    exact hk t ht _ _ _

end PoincareConjecture.M47
