import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.RawDistanceContinuity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.BasePointDistanceSupport
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.ScalarJetLinearity

/-!
# Growing distance supports at every raw-flow point

Morgan-Tian, Section 12.5, p. 304: the complete maximum principle uses a
growing function with smooth upper supports at every contact point.
Positive-distance supports come from M04 and the raw time comparison;
at the base point the inverse exponential quadratic supplies the missing
support. Thus no cut-locus or base-point exclusion survives here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.M35.Uniqueness

/-- Section 12.5, p. 304: the actual growing barrier is one at its center. -/
theorem rawDistanceSquare_self {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (p : StandardCapSpace) (t : ℝ) :
    rawDistanceSquare G p t p = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨(G.flow.metric t).toRiemannianMetric⟩
  have hh : (G.flow.metric t).edist p p = 0 := Manifold.riemannianEDist_self
  simp [rawDistanceSquare, hh]

/-- Section 12.5, p. 304: a slab-dependent constant controls actual
spacetime upper supports of the growing barrier at every raw-flow point. -/
theorem exists_complete_distance_square_supports
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc 0 T, ∀ p q : StandardCapSpace, ∀ ε > 0,
        ∃ ψ : ℝ → StandardCapSpace → ℝ, ∃ v : ℝ,
          ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (ψ t) q ∧
          ψ t q = rawDistanceSquare G p t q ∧
          (∀ᶠ y in 𝓝 q, rawDistanceSquare G p t y ≤ ψ t y) ∧
          (∀ s ∈ Icc 0 t, rawDistanceSquare G p s q ≤ ψ s q) ∧
          HasDerivAt (fun s => ψ s q) v t ∧
          -C * rawDistanceSquare G p t q - ε ≤
            v - (G.flow.connection t).laplacian (ψ t) q := by
  obtain ⟨K, hK, hsupp⟩ := exists_raw_distance_square_supports P G hT hTlt
  refine ⟨12 * K + 8, by positivity, ?_⟩
  intro t ht p q ε hε
  by_cases hd : 0 < ((G.flow.metric t).edist p q).toReal
  · exact hsupp t ht p q hd ε hε
  have hpq : p = q := by
    let : MetricSpace StandardCapSpace := Proofs.M09.selectedMetricSpace (G.flow.metric t)
    apply dist_eq_zero.mp
    exact le_antisymm (not_lt.mp hd) ENNReal.toReal_nonneg
  subst q
  obtain ⟨u, hu, hup, hupper, hlap⟩ := exists_distance_square_base_support
    (G.flow.metric t) (G.flow.connection t) (G.complete P ⟨ht.1, ht.2.trans_lt hTlt⟩) p
  refine ⟨fun _ y => 1 + u y, 0, contMDiffAt_const.add hu, ?_, ?_, ?_,
    hasDerivAt_const t (1 + u p), ?_⟩
  · change 1 + u p = rawDistanceSquare G p t p
    rw [hup, add_zero, rawDistanceSquare_self]
  · filter_upwards [hupper] with y hy
    exact add_le_add (le_refl 1) hy
  · intro s _
    change rawDistanceSquare G p s p ≤ 1 + u p
    rw [rawDistanceSquare_self, hup, add_zero]
  · rw [rawDistanceSquare_self, laplacian_const_add_at _ hu 1, hlap]
    nlinarith

end PoincareMT.M35.Uniqueness
