import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Functionals
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.Continuity
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.FixedMap
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.MinimalVariation



set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture





theorem m60AreaCore_of_leastSphere
    (tensor : ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus)
    (scalar : ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (J : Set ℝ) (F : RicciFlow n M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ))
    (least : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric n M),
      IsCompact (Set.univ : Set M) → ∀ x : M,
        Nontrivial (HomotopyGroup.Pi 2 M x) → M60LeastSphereAreaConclusion g) :
    M60AreaCore.{u} := by
  refine ⟨?_, ?_, least, ?_, ?_⟩
  · intro n M _ _ _ _ _ g f hf
    exact m60SphereAreaProperties_of_contMDiff g f hf
  · intro M _ _ _ _ _ g hcompact
    exact m60FillingAreaProperties_of_compact g hcompact
  · intro n M _ _ _ _ _ a b hab F _ D hD hnorm f hf
    exact m60FixedMapAreaProperties_of_ricci_bound hab F
      (fun t _ => tensor n M (F.metric t) (F.connection t)) D hD hnorm f hf
  · intro M _ _ _ _ _ a b hab F hcompact f t ht hf
    exact m60MinimalSphereVariationProperties_of_compact hab F hcompact
      (fun s _ => tensor 3 M (F.metric s) (F.connection s))
      (scalar 3 M (Set.Icc a b) F) f t ht hf

end PoincareConjecture
