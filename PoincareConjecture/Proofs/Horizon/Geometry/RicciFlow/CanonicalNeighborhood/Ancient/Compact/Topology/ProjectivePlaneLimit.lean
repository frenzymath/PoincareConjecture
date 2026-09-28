import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Topology.Embedding
import PoincareConjecture.Definitions.M26CanonicalNeighborhoods










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

private noncomputable def halfInterval : Ioo (-1 : ℝ) 1 → Ioo (-1 : ℝ) 1 :=
  fun x => ⟨x.val / 2, by constructor <;> linarith [x.property.1, x.property.2]⟩

private theorem halfInterval_isOpenEmbedding : Topology.IsOpenEmbedding halfInterval := by
  apply isOpen_Ioo.isOpenEmbedding_subtypeVal.of_comp halfInterval
  convert
    (Homeomorph.mulRight₀ (2 : ℝ)⁻¹ (by norm_num)).isOpenEmbedding.comp
      (isOpen_Ioo (a := (-1 : ℝ)) (b := 1)).isOpenEmbedding_subtypeVal using 1
  ext x
  simp [halfInterval, div_eq_mul_inv]

private theorem exists_precompact_projective_collar
    {M : Type*} [TopologicalSpace M]
    (f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → M)
    (hf : Topology.IsOpenEmbedding f) :
    ∃ (g : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → M) (C : Set M),
      Topology.IsOpenEmbedding g ∧ IsCompact C ∧ range g ⊆ C := by
  let i : Icc (-1 / 2 : ℝ) (1 / 2) → Ioo (-1 : ℝ) 1 :=
    fun x => ⟨x.val, by constructor <;> linarith [x.property.1, x.property.2]⟩
  let F : RealProjectiveTwo × Icc (-1 / 2 : ℝ) (1 / 2) → M :=
    fun p => f (p.1, i p.2)
  have hF : Continuous F := hf.continuous.comp
    (continuous_fst.prodMk (continuous_snd.subtype_val.subtype_mk _))
  refine ⟨f ∘ Prod.map id halfInterval, range F,
    hf.comp (Topology.IsOpenEmbedding.id.prodMap halfInterval_isOpenEmbedding),
    isCompact_range hF, ?_⟩
  rintro _ ⟨⟨p, s⟩, rfl⟩
  refine ⟨(p, ⟨s.val / 2, ?_⟩), rfl⟩
  constructor <;> linarith [s.property.1, s.property.2]

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalExtension



theorem noEmbeddedTrivialNormalProjectivePlane
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hsource : ∀ k, NoEmbeddedTrivialNormalProjectivePlane (S.term k).flow) :
    NoEmbeddedTrivialNormalProjectivePlane G.limit.flow := by
  rintro ⟨f, hf⟩
  obtain ⟨g, C, hg, hC, hrange⟩ := exists_precompact_projective_collar f hf
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hC
  obtain ⟨e, _, _, _⟩ := T.terminal_embedding
  let E := (e j).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open j)
  have hgs (p : RealProjectiveTwo × Ioo (-1 : ℝ) 1) : g p ∈ E.source :=
    hj (hrange (mem_range_self p))
  let g' : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → E.source := fun p => ⟨g p, hgs p⟩
  have hg' : Topology.IsOpenEmbedding g' :=
    E.open_source.isOpenEmbedding_subtypeVal.of_comp g' hg
  apply hsource (G.subsequence j)
  exact ⟨E ∘ g, E.isOpenEmbedding_restrict.comp hg'⟩

end M23TerminalExtension

end PoincareConjecture
