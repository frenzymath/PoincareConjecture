import PoincareConjecture.Definitions.M11CompatibleEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}

theorem intervalInclusion_embedding (S : SpacetimeIntervalSystem)
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain) :
    IsEmbedding (spacetimeIntervalInclusion (S.interval L) (S.interval K) h) :=
  IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal

theorem intervalInclusion_differential_injective (S : SpacetimeIntervalSystem)
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain) (t : (S.interval L).Point) :
    Function.Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1)
      (spacetimeIntervalInclusion (S.interval L) (S.interval K) h) t) := by
  let := (S.interval L).chartedSpace
  let := (S.interval K).chartedSpace
  let j := spacetimeIntervalInclusion (S.interval L) (S.interval K) h
  have ht (v : EuclideanSpace ℝ (Fin 1)) :
      (S.interval L).inclusionDerivative t v =
        (S.interval K).inclusionDerivative (j t) (mfderiv (𝓡∂ 1) (𝓡∂ 1) j t v) := by
    change ((S.interval L).inclusionDerivative t).toContinuousLinearMap v =
      ((S.interval K).inclusionDerivative (j t)).toContinuousLinearMap
        (mfderiv (𝓡∂ 1) (𝓡∂ 1) j t v)
    rw [(S.interval L).inclusionDerivative_eq, (S.interval K).inclusionDerivative_eq]
    exact mfderiv_comp_apply t
      (((S.interval K).inclusion_smooth (j t)).mdifferentiableAt (by simp))
      ((S.inclusion_smooth L K h t).mdifferentiableAt (by simp)) v
  intro v w hvw
  apply ((S.interval L).inclusionDerivative t).injective
  rw [ht, ht, hvw]

noncomputable def embeddingTimeRestrict (S : SpacetimeIntervalSystem)
    {C : Type*} [TopologicalSpace C] (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (e : CompatibleSpacetimeEmbedding F (S.interval K) C) :
    CompatibleSpacetimeEmbedding F (S.interval L) C where
  interval_subset := fun _ ht ↦ e.interval_subset (h ht)
  toSpacetime := fun p ↦ e.toSpacetime
    (spacetimeIntervalInclusion (S.interval L) (S.interval K) h p.1, p.2)
  embedding := e.embedding.comp ((intervalInclusion_embedding S K L h).prodMap IsEmbedding.id)
  time_eq := fun p ↦ e.time_eq
    (spacetimeIntervalInclusion (S.interval L) (S.interval K) h p.1, p.2)
  worldline_smooth := fun x ↦ (e.worldline_smooth x).comp (S.inclusion_smooth L K h)
  worldline_derivative := by
    intro t x
    have hc := mfderiv_comp_apply t
      ((e.worldline_smooth x _).mdifferentiableAt (by simp))
      ((S.inclusion_smooth L K h t).mdifferentiableAt (by simp))
      ((S.interval L).positiveTangent t)
    rw [S.inclusion_derivative, e.worldline_derivative] at hc
    exact hc

noncomputable def cylinderTimeRestrict (S : SpacetimeIntervalSystem)
    {C : Type*} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (e : CompatibleSpacetimeCylinder F (S.interval K) C) :
    CompatibleSpacetimeCylinder F (S.interval L) C where
  toCompatibleSpacetimeEmbedding := embeddingTimeRestrict S K L h e.toCompatibleSpacetimeEmbedding
  smooth := e.smooth.comp ((S.inclusion_smooth L K h).prodMap contMDiff_id)
  differential_injective := by
    intro p
    let j := spacetimeIntervalInclusion (S.interval L) (S.interval K) h
    have hd : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) j p.1 :=
      (S.inclusion_smooth L K h p.1).mdifferentiableAt (by simp)
    have hj : Function.Injective
        (mfderiv (spacetimeModel n) (spacetimeModel n) (Prod.map j (id : C → C)) p) := by
      rw [mfderiv_prodMap hd mdifferentiableAt_id, mfderiv_id]
      intro v w hvw
      have h₁ := congrArg Prod.fst hvw
      have h₂ := congrArg Prod.snd hvw
      apply Prod.ext
      · exact intervalInclusion_differential_injective S K L h p.1 h₁
      · exact h₂
    change Function.Injective
      (mfderiv (spacetimeModel n) (spacetimeModel n) (e.toSpacetime ∘ Prod.map j id) p)
    rw [mfderiv_comp p ((e.smooth _).mdifferentiableAt (by simp))
      (hd.prodMap mdifferentiableAt_id)]
    exact (e.differential_injective _).comp hj

end PoincareConjecture.Proofs.M11
