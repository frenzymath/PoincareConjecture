import PoincareConjecture.Proofs.M47.LimitCanonicalComponentSectionalTolerance
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_TwoJetModulus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

open M04 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem limitCanonical_component_eventually_sectional_lower
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    {g : ∀ k, RiemannianMetric 3 (M k)} (D : ∀ k, LeviCivitaData (g k))
    {g0 : RiemannianMetric 3 X} (D0 : LeviCivitaData g0)
    (f : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) E (M k) ∞)
    (f0 : PartialDiffeomorph (𝓡 3) (𝓡 3) E X ∞)
    {K : Set E} (hK : IsCompact K) (hK0 : K ⊆ f0.source)
    (hsource : ∀ᶠ k in atTop, K ⊆ (f k).source)
    (hjet : ∀ j ≤ 2, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients (f k)))
      (iteratedFDeriv ℝ j (g0.pullbackCoefficients f0)) atTop K)
    (a : ℝ) (hsec : ∀ x ∈ K, ∀ u v : TangentSpace (𝓡 3) (f0 x),
      LeviCivitaData.IsOrthonormalPair g0 (f0 x) u v → a < D0.sectionalCurvature (f0 x) u v) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      (∀ u v : TangentSpace (𝓡 3) (f k x),
        a * metricGram (g k) (f k x) u v ≤ (D k).curvatureTensor (f k x) u v u v) ∧
      (∀ u v : TangentSpace (𝓡 3) (f k x),
        LeviCivitaData.IsOrthonormalPair (g k) (f k x) u v →
          a ≤ (D k).sectionalCurvature (f k x) u v) ∧
      6 * a ≤ (D k).scalarCurvature (f k x) := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    limitCanonical_component_sectional_jet_tolerance D0 f0 hK hK0 a hsec
  have htail : ∀ᶠ k in atTop, ∀ j : Fin 3, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ (j : ℕ) ((g k).pullbackCoefficients (f k)) x -
        iteratedFDeriv ℝ (j : ℕ) (g0.pullbackCoefficients f0) x‖ ≤ delta := by
    apply eventually_all.mpr
    intro j
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hjet j (by omega)) delta hdelta] with k hk x hx
    simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le
  filter_upwards [hsource, htail] with k hk hkj x hx
  have htwo := norm_metricTwoJet_sub_le ((g k).pullbackCoefficients (f k))
    (g0.pullbackCoefficients f0) x (fun j hj => hkj ⟨j, by omega⟩ x hx)
  have hJ := hbound x hx _ htwo
  exact ⟨limitCanonical_component_all_planes_of_model_jets (D k) (f k) (hk hx) a hJ,
    limitCanonical_component_curvature_of_model_jets (D k) (f k) (hk hx) a hJ⟩

end PoincareConjecture.M47
