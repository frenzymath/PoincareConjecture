import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallInitialSides
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallRecut
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallRecutDiameter

/-!
# The actual finite-diameter recut with its retained source orientation

Initial source graphs, the same ambient recut and its actual intrinsic
diameter are constructed together. Source: Morgan--Tian Proposition
10.7 and Claim 10.8, pp. 253-254; M28 derivations 161a and 161b.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 3200000 in
-- Each retained geometric field uses the literal first-limit instances.
/-- The actual positive recut retains precisely the original-source and
intrinsic-geometric outputs used by the final proof. Its producer below
constructs every field. Source: MT pp. 253-254; derivations 161a and 161b. -/
structure RetainedPositiveRecutData
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k)))
    (D0 : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      LeviCivitaData G.limitMetric) where
  /-- The fixed original limiting neck used to label the source sides. -/
  initial : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    EpsilonNeck G.limitMetric
  /-- Its center is the actual base of the retained spatial limit. -/
  initial_center : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    initial.center = G.base
  /-- One source orientation is retained for all positive-side points. -/
  sigma : ℕ → ℕ
  /-- The orientation selection is cofinal in the retained source. -/
  sigma_strictMono : StrictMono sigma
  /-- Literal source graphs of the same fixed limiting central sphere. -/
  graphs : ℕ → UnitTwoSphere → ℝ
  /-- Each original graph is smooth. -/
  graphs_smooth : ∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (graphs k)
  /-- All graphs stay in the fixed narrow original initial slab. -/
  graphs_height : ∀ k z, |graphs k z| < epsilon⁻¹ / 32
  /-- The raw source image of the fixed sphere is exactly the graph. -/
  graphs_image : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
      W.high_index G (sigma k)) '' initial.central_sphere =
        range (fun z =>
          ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
            (z, graphs k z))
  /-- The actual positive-side ordinary-neck cover from original source necks. -/
  cover : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    NeckOnlyCover G.limitMetric
  /-- The limit cover has twice the original accuracy parameter. -/
  cover_epsilon : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    cover.epsilon = 2 * epsilon
  /-- Every cover neck retains the chosen ambient scalar connection. -/
  cover_connection : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ N ∈ cover.necks, N.connection = D0
  /-- The corrected Appendix-A construction for this same actual cover. -/
  tube : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    CorrectedA19Conclusion G.limitMetric cover
  /-- The original open positive recut on which intrinsic distances are tested. -/
  region : letI := G.limitCarrier.topologicalSpace
    TopologicalSpace.Opens G.limitCarrier.carrier
  /-- Its points retain the centered-neck cover. -/
  region_subset : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    (region : Set G.limitCarrier.carrier) ⊆ cover.X
  /-- Every fixed recut point has the same positive original-source label. -/
  source_side : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ x ∈ (region : Set G.limitCarrier.carrier), ∀ᶠ k in atTop,
      (G.embedding (sigma k) x).val.val ∉
        ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28 (graphs k)
  /-- The ambient cylinder realizing this precise recut as a tail. -/
  model : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    OpenCylinderModel tube.tube.carrier
  /-- The open region is the literal half-tail in the ambient cylinder. -/
  region_tail : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    (region : Set G.limitCarrier.carrier) = model.tail true (1 / 2)
  /-- The global frontier is the compact middle sphere of that cylinder. -/
  frontier_eq : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    frontier (region : Set G.limitCarrier.carrier) = model.middleSphere
  /-- The recut sphere retains the selected tube's sphere-isotopy class. -/
  model_isotopy : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    SmoothSphereIsotopicIn tube.tube.carrier model.middleSphere
      tube.tube.cylinder.middleSphere
  /-- Even the closure of the recut stays inside the original tube. -/
  closure_subset : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    closure (region : Set G.limitCarrier.carrier) ⊆ tube.tube.carrier
  /-- The ambient scalar is uniformly positive on the whole recut. -/
  scalar_lower : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ x ∈ (region : Set G.limitCarrier.carrier), 3 ≤ D0.scalarCurvature x
  /-- Scalar divergence is uniform in the same ambient cylinder height. -/
  scalar_diverges : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ bound : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ tube.tube.carrier, d < (model.inverse x).2 → bound < D0.scalarCurvature x
  /-- A bound obtained from the actual confined original-source competitors. -/
  diameter : ℝ
  /-- The diameter bound is positive. -/
  diameter_pos : 0 < diameter
  /-- The bound is on the literal recut intrinsic diameter. -/
  diameter_bound : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    intrinsicDiameter G.limitMetric (region : Set G.limitCarrier.carrier) ≤
      ENNReal.ofReal diameter

set_option maxHeartbeats 4800000 in
-- All three producers share the dependent retained source family and metric.
/-- Actual initial sides, the ambient recut and its confined intrinsic
diameter construct one retained packet. Its source graphs and initial
neck are unchanged. Source: MT pp. 253-254; derivations 161a and 161b. -/
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

end PoincareMT.M28.CounterexampleNeckFamily
