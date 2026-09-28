import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph
import PoincareConjecture.Definitions.M11CompatibleEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Topology
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {D : SmoothSpacetimeInterval K}

noncomputable def embeddingSourceRestrict {C C' : Type*}
    [TopologicalSpace C] [TopologicalSpace C'] (e : CompatibleSpacetimeEmbedding F D C)
    (j : C' → C) (hj : IsEmbedding j) : CompatibleSpacetimeEmbedding F D C' where
  interval_subset := e.interval_subset
  toSpacetime := fun p ↦ e.toSpacetime (p.1, j p.2)
  embedding := e.embedding.comp (IsEmbedding.id.prodMap hj)
  time_eq := fun p ↦ e.time_eq (p.1, j p.2)
  worldline_smooth := fun x ↦ e.worldline_smooth (j x)
  worldline_derivative := fun t x ↦ e.worldline_derivative t (j x)

noncomputable def cylinderOpenRestrict {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder F D C) (U : TopologicalSpace.Opens C) :
    CompatibleSpacetimeCylinder F D U where
  toCompatibleSpacetimeEmbedding := embeddingSourceRestrict e.toCompatibleSpacetimeEmbedding
    Subtype.val IsEmbedding.subtypeVal
  smooth := e.smooth.comp (contMDiff_id.prodMap contMDiff_subtype_val)
  differential_injective := by
    intro p
    have hd : MDifferentiableAt (𝓡 n) (𝓡 n) (Subtype.val : U → C) p.2 :=
      contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
    have hj : Function.Injective
        (mfderiv (spacetimeModel n) (spacetimeModel n)
          (Prod.map (id : D.Point → D.Point) (Subtype.val : U → C)) p) := by
      rw [mfderiv_prodMap mdifferentiableAt_id hd, mfderiv_id]
      intro v w hvw
      have h₁ := congrArg Prod.fst hvw
      have h₂ := congrArg Prod.snd hvw
      apply Prod.ext
      · exact h₁
      · exact openSubset_differential_injective U p.2 h₂
    change Function.Injective (mfderiv (spacetimeModel n) (spacetimeModel n)
      (e.toSpacetime ∘ Prod.map id (Subtype.val : U → C)) p)
    rw [mfderiv_comp p ((e.smooth _).mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMap hd)]
    exact (e.differential_injective _).comp hj

end PoincareConjecture.Proofs.M11
