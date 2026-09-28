import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Statements.Ch04.CurvatureTheory









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.PartialStandardCapFlow



theorem exists_metric_comparison
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T, ∀ x : StandardCapSpace,
      ∀ v : TangentSpace (𝓡 3) x,
        Real.exp (-6 * K * t) * g₀.metric.inner x v v ≤
            (G.flow.metric t).inner x v v ∧
          (G.flow.metric t).inner x v v ≤
            Real.exp (6 * K * t) * g₀.metric.inner x v v := by
  obtain ⟨K, hK, hbound⟩ := G.curvature_locally_bounded T hT hTlt
  refine ⟨K, hK, ?_⟩
  intro t ht x v
  have hcompare := P.metric_comparison 3 StandardCapSpace
    (Set.Ico 0 G.lifetime) G.flow 0 t K
    ⟨le_rfl, G.lifetime_pos⟩ ⟨ht.1, ht.2.trans_lt hTlt⟩ ht.1 hK
    (fun s hs y => (le_abs_self _).trans (hbound s ⟨hs.1, hs.2.trans ht.2⟩ y)) x v
  simpa only [G.initial_metric, Nat.cast_ofNat, sub_zero, neg_mul,
    show (2 : ℝ) * 3 = 6 by norm_num] using hcompare

end PoincareConjecture.PartialStandardCapFlow
