import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.FixedMap
import PoincareConjecture.Proofs.M04.ScalarEvolutionCoefficients











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60_exists_uniform_ricci_bound {J : Set ℝ} (F : RicciFlow n M J)
    (hJ : IsCompact J) (hcompact : IsCompact (univ : Set M)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ J, ∀ x : M, (F.connection t).ricciNormSq x ≤ D ^ 2 := by
  obtain ⟨C, hC⟩ := (hJ.prod hcompact).exists_bound_of_continuousOn
    (M04.continuousOn_flow_ricciNormSq F)
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro t ht x
  have hnorm : (F.connection t).ricciNormSq x ≤ max C 1 :=
    (le_abs_self _).trans ((hC (t, x) ⟨ht, mem_univ x⟩).trans (le_max_left _ _))
  have hlarge : 1 ≤ max C 1 := le_max_right _ _
  nlinarith




theorem m60SphereArea_variation_on_compact {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (htensor : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    ∀ t ∈ Icc a b,
      Integrable (m60SphereRicciTraceDensity (F.connection t) f) volume ∧
      HasDerivWithinAt (fun s => m60SphereArea (F.metric s) f)
        (-(∫ z : LoopPlane, m60SphereRicciTraceDensity (F.connection t) f z ∂volume))
        (Icc a b) t := by
  obtain ⟨D, hD, hnorm⟩ := m60_exists_uniform_ricci_bound F isCompact_Icc hcompact
  have h := m60FixedMapAreaProperties_of_ricci_bound hab F htensor D hD hnorm f hf
  exact fun t ht => ⟨h.ricci_trace_integrable t ht, h.variation t ht⟩

end PoincareConjecture
