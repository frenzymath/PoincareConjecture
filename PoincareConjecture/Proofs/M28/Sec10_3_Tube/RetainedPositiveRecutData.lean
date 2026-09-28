import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialSides
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRecut
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRecutDiameter

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 3200000 in

structure RetainedPositiveRecutData
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k)))
    (D0 : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      LeviCivitaData G.limitMetric) where

  initial : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    EpsilonNeck G.limitMetric

  initial_center : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    initial.center = G.base

  sigma : ℕ → ℕ

  sigma_strictMono : StrictMono sigma

  graphs : ℕ → UnitTwoSphere → ℝ

  graphs_smooth : ∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (graphs k)

  graphs_height : ∀ k z, |graphs k z| < epsilon⁻¹ / 32

  graphs_image : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
      W.high_index G (sigma k)) '' initial.central_sphere =
        range (fun z =>
          ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
            (z, graphs k z))

  cover : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    NeckOnlyCover G.limitMetric

  cover_epsilon : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    cover.epsilon = 2 * epsilon

  cover_connection : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ N ∈ cover.necks, N.connection = D0

  tube : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    CorrectedA19Conclusion G.limitMetric cover

  region : letI := G.limitCarrier.topologicalSpace
    TopologicalSpace.Opens G.limitCarrier.carrier

  region_subset : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    (region : Set G.limitCarrier.carrier) ⊆ cover.X

  source_side : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ x ∈ (region : Set G.limitCarrier.carrier), ∀ᶠ k in atTop,
      (G.embedding (sigma k) x).val.val ∉
        ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28 (graphs k)

  model : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    OpenCylinderModel tube.tube.carrier

  region_tail : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    (region : Set G.limitCarrier.carrier) = model.tail true (1 / 2)

  frontier_eq : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    frontier (region : Set G.limitCarrier.carrier) = model.middleSphere

  model_isotopy : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    SmoothSphereIsotopicIn tube.tube.carrier model.middleSphere
      tube.tube.cylinder.middleSphere

  closure_subset : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    closure (region : Set G.limitCarrier.carrier) ⊆ tube.tube.carrier

  scalar_lower : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ x ∈ (region : Set G.limitCarrier.carrier), 3 ≤ D0.scalarCurvature x

  scalar_diverges : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ bound : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ tube.tube.carrier, d < (model.inverse x).2 → bound < D0.scalarCurvature x

  diameter : ℝ

  diameter_pos : 0 < diameter

  diameter_bound : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    intrinsicDiameter G.limitMetric (region : Set G.limitCarrier.carrier) ≤
      ENNReal.ofReal diameter

set_option maxHeartbeats 4800000 in

theorem exists_retained_positive_recut_data_accuracy (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ D0 : LeviCivitaData G.limitMetric,
            Nonempty (RetainedPositiveRecutData H W G D0) := by
  obtain ⟨epsilonI, hIpos, _hIsmall, hinitial⟩ := exists_retained_initial_sides_accuracy.{u}
  obtain ⟨epsilonR, hRpos, hRsmall, hrecut⟩ := exists_retained_smooth_recut_ambient_accuracy P
  obtain ⟨epsilonD, hDpos, _hDsmall, hdiameter⟩ := exists_retained_recut_diameter_accuracy P
  refine ⟨min epsilonI (min epsilonR epsilonD), lt_min hIpos (lt_min hRpos hDpos),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hRsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  intro D0
  obtain ⟨j0, L, hLeps, hLcenter, _hLscale, _hLD, hLstage, hLsep,
    sigma, hsigma, Uminus, Uplus, _hminusOpen, hplusOpen, hminusConn, hplusConn,
    hdisjoint, hunion, _hfrontMinus, hfrontPlus, hclMinus, _hclPlus,
    _hminusScalar, f, hf, _hminusLabel, hplusLabel⟩ :=
      hinitial H (hepsilon.trans (min_le_left _ _)) W G D0
  have hcomplement : Uplusᶜ = closure Uminus := by
    rw [hclMinus]
    ext x
    constructor
    · intro hx
      by_cases hxS : x ∈ L.central_sphere
      · exact Or.inr hxS
      · have hxUnion : x ∈ Uminus ∪ Uplus := by rw [hunion]; exact hxS
        exact Or.inl (hxUnion.resolve_right hx)
    · rintro (hx | hx) hplus
      · exact Set.disjoint_left.mp hdisjoint hx hplus
      · have hnot : x ∈ L.central_sphereᶜ := hunion ▸ (Or.inr hplus : x ∈ Uminus ∪ Uplus)
        exact hnot hx
  have hcompl : IsPreconnected Uplusᶜ := by
    rw [hcomplement]
    exact hminusConn.isPreconnected.closure
  have hfSmooth (k : ℕ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k) := (hf k).2.1
  have hfHeight (k : ℕ) (z : UnitTwoSphere) : |f k z| < epsilon⁻¹ / 32 :=
    (hf k).2.2.1 z
  have hfGraph (k : ℕ) :
      (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma k)) '' L.central_sphere =
          range (fun z =>
            ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
              (z, f k z)) := (hf k).2.2.2
  have hpositiveSide (x : G.limitCarrier.carrier) (hx : x ∈ Uplus) :
      ∀ᶠ k in atTop, (G.embedding (sigma k) x).val.val ∉
        ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28 (f k) := by
    simpa only [regularRawStageDiffeomorph_apply] using hplusLabel x hx
  obtain ⟨K, hKX, hKe, hKD, T, _i, _hi, N, _hsame, _hNX,
    Y, hYo, _hYc, hYX, hYcl, a, b, _ha, ha0, hb0, _hb,
    U, hU, hUX, _hSV, hfront, _hadded, B, hBS, hUtail,
    _hNisotopy, hBisotopy, hclosure, hdiverge, _Z, hlower, _hinit, _hend, _hnecks⟩ :=
      hrecut H W (hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _)))
        G D0 L hLcenter hLeps hLsep Uplus hplusOpen hplusConn hcompl hfrontPlus
        sigma hsigma f hfSmooth hfHeight hfGraph hpositiveSide
  obtain ⟨Bdiam, hBdiam, hdiam⟩ :=
    hdiameter H W (hepsilon.trans ((min_le_right _ _).trans (min_le_right _ _)))
      G D0 L j0 hLcenter hLstage sigma hsigma f hfSmooth hfHeight hfGraph
      Uplus hpositiveSide N Y hYo hYX hYcl a b ha0 hb0 U hU hUX
  refine ⟨{
    initial := L
    initial_center := hLcenter
    sigma := sigma
    sigma_strictMono := hsigma
    graphs := f
    graphs_smooth := hfSmooth
    graphs_height := hfHeight
    graphs_image := hfGraph
    cover := K
    cover_epsilon := hKe
    cover_connection := hKD
    tube := T
    region := U
    region_subset := by rw [hKX]; exact hUX
    source_side := fun x hx => hpositiveSide x (hUX hx)
    model := B
    region_tail := hUtail
    frontier_eq := hfront.trans hBS.symm
    model_isotopy := hBisotopy
    closure_subset := hclosure
    scalar_lower := hlower
    scalar_diverges := hdiverge
    diameter := Bdiam
    diameter_pos := hBdiam
    diameter_bound := hdiam }⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
