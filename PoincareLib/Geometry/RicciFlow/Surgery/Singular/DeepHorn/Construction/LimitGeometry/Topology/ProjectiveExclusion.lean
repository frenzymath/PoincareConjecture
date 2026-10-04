import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Topology.HornOrientation
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Charts.ForwardComparison
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.HornBalls

/-!
# The actual horn limit has no projective-plane product neighborhood

Morgan--Tian Claim 11.34 and its convergence paragraph, printed pp. 288-289.
A compact half-collar of any hypothetical projective-plane neighborhood
passes through the retained M30 embeddings into the actual source horns.
Their orientation obstruction rules it out without assuming simple
connectivity of the limit or any roundness of a compact factor.

The source horn argument is rederived in `HornOrientation.lean` from the
read-only DeepHorn `StrongHorn.noTrivialNormalProjectivePlane_interior`.
The retained embeddings and confinement are the owned ForwardComparison
and HornBalls statements. No Surgery or compatibility donor is imported.
Reviewed gap repair:
`proof-work/tasks/M32/derivations/claim11_34-horn-projective-exclusion.md`.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M32

private noncomputable def halfInterval : Ioo (-1 : ℝ) 1 → Ioo (-1 : ℝ) 1 :=
  fun s => ⟨(1 / 2 : ℝ) * s, by
    constructor <;> linarith [s.property.1, s.property.2]⟩

private theorem halfInterval_isOpenEmbedding : IsOpenEmbedding halfInterval := by
  let e := Homeomorph.mulLeft₀ (1 / 2 : ℝ) (by norm_num)
  have h : IsOpenEmbedding (fun s : Ioo (-1 : ℝ) 1 => (1 / 2 : ℝ) * (s : ℝ)) :=
    e.isOpenEmbedding.comp isOpen_Ioo.isOpenEmbedding_subtypeVal
  exact IsOpenEmbedding.of_comp halfInterval isOpen_Ioo.isOpenEmbedding_subtypeVal h

private theorem projective_compact_half_collar
    {Y : Type u} [TopologicalSpace Y]
    (f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → Y) (hf : IsOpenEmbedding f) :
    ∃ g : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → Y,
      IsOpenEmbedding g ∧ ∃ K : Set Y, IsCompact K ∧ range g ⊆ K := by
  have hsub : Icc (-1 / 2 : ℝ) (1 / 2) ⊆ Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let inc : Icc (-1 / 2 : ℝ) (1 / 2) → Ioo (-1 : ℝ) 1 := Set.inclusion hsub
  let c : RealProjectiveTwo × Icc (-1 / 2 : ℝ) (1 / 2) → Y :=
    fun z => f (z.1, inc z.2)
  have hc : Continuous c :=
    hf.continuous.comp (continuous_id.prodMap (continuous_inclusion hsub))
  let g : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → Y :=
    fun z => f (z.1, halfInterval z.2)
  refine ⟨g, hf.comp (IsOpenEmbedding.id.prodMap halfInterval_isOpenEmbedding),
    range c, isCompact_range hc, ?_⟩
  rintro y ⟨⟨q, s⟩, rfl⟩
  have hs : (1 / 2 : ℝ) * (s : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    constructor <;> linarith [s.property.1, s.property.2]
  exact ⟨(q, ⟨(1 / 2 : ℝ) * (s : ℝ), hs⟩), rfl⟩

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
  (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
  (Q : ∀ k, SingularLimitConclusion (H k))
  (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
  (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
  (hdiv : Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)

/-- The retained terminal convergence admits no open projective-plane product.
The actual source horns may have arbitrary varying accuracies, and the original
subsequence and zero-time maps are retained throughout the argument.
Source: Claim 11.33, p. 288; Claim 11.34 and its convergence paragraph,
pp. 288-289; Theorem 0.3, footnote 2, p. xii.
Gap repair: `claim11_34-horn-projective-exclusion.md`, section 5. -/
theorem terminalBlowupConvergence_no_projective_product
    (hM04 : RicciFlowCurvatureTheory.{u}) {K B : ℝ} {accuracy : ℕ → ℝ}
    (hK : 0 < K) (hB : 0 < B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (horn : ∀ k, StrongHorn (Q k).extension (accuracy k))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K)
    {J : Set ℝ}
    (G : GeneralizedBlowupConvergence (terminalBlowupSequence H Q x hpos hdiv) J) :
    ¬ ∃ f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → G.limit.carrier.carrier,
      IsOpenEmbedding f := by
  rintro ⟨f, hf⟩
  obtain ⟨fhalf, hfhalf, C, hC, hhalf⟩ := projective_compact_half_collar f hf
  let g := G.limit.flow.metric 0
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  obtain ⟨r, hr, hCr⟩ := hC.isBounded.subset_ball_lt 0 G.limit.base
  rw [g.toMetricSpace_ball] at hCr
  have hforward := blowup_eventually_zeroSliceEmbedding_image_ball G hr
    (by norm_num : (1 : ℝ) < 2)
  have hhorn := terminalBlowupSequence_baseBalls_subset_horns H Q x hpos hdiv hM04
    hK hB hcutoff hconstant horn hx hboundary (2 * r) (by positivity)
  have hhorn' := G.subsequence_strictMono.tendsto_atTop.eventually hhorn
  obtain ⟨k, hforwardk, hhornk⟩ := (hforward.and hhorn').exists
  let e := blowup_zeroSliceEmbedding G k
  have hsource (z : RealProjectiveTwo × Ioo (-1 : ℝ) 1) : fhalf z ∈ e.source :=
    hforwardk.1 (hCr (hhalf (mem_range_self z)))
  let fsource : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → e.source :=
    fun z => ⟨fhalf z, hsource z⟩
  have hfsource : IsOpenEmbedding fsource :=
    IsOpenEmbedding.of_comp fsource e.open_source.isOpenEmbedding_subtypeVal hfhalf
  let fout : RealProjectiveTwo × Ioo (-1 : ℝ) 1 →
      ((Q (G.subsequence k)).extension.extended.slice (T (G.subsequence k))).carrier :=
    fun z => e (fsource z)
  have hfout : IsOpenEmbedding fout := e.isOpenEmbedding_restrict.comp hfsource
  have hout : range fout ⊆ (horn (G.subsequence k)).carrier := by
    rintro y ⟨z, rfl⟩
    apply hhornk
    apply hforwardk.2
    exact ⟨fhalf z, hCr (hhalf (mem_range_self z)), rfl⟩
  exact horn_no_projective_product (horn (G.subsequence k)) ⟨fout, hfout, hout⟩

end PoincareMT.M32
