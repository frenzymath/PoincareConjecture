import PoincareConjecture.Proofs.M15.Mathlib.CurveExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction
import PoincareConjecture.Definitions.Ch06.LGeometry

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RiemannianMetric

theorem exists_smooth_short_curve
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p q : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) (hq : q ∈ g.ball p R) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ) (𝓡 n) ∞ γ ∧
      γ 0 = p ∧ γ 1 = q ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (γ t) (curveVelocity γ t) ≤ R := by
  obtain ⟨ε, hε, η, hη, hη0, hη1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball p q hR hcompact hq
  have hηsmooth : ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ η (Ioo (-ε) (1 + ε)) :=
    fun t ht => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hη ht).contMDiffWithinAt
  obtain ⟨C, hC⟩ := hη.exists_constant_tangentNorm (by linarith)
  have hCdist : ENNReal.ofReal (C : ℝ) = g.edist p q := by
    have hlength := g.pathELength_eq_of_tangentNorm_eq (C := (C : ℝ))
      (fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
        hC t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hlength' := hη.pathELength_eq_of_edist_segment hε hη0 hmin
    simpa only [sub_zero, ENNReal.ofReal_one, mul_one] using hlength.symm.trans hlength'
  have hCR : (C : ℝ) < R := by
    have hd : ENNReal.ofReal (C : ℝ) < ENNReal.ofReal R := by
      rw [hCdist]
      exact hq
    simpa only [ENNReal.toReal_ofReal C.coe_nonneg] using
      ENNReal.toReal_lt_of_lt_ofReal hd
  have hsub : Icc (-ε / 2) (1 + ε / 2) ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨γ, hγ, heq⟩ := hηsmooth.exists_global_extension_Icc
    (by linarith : -ε / 2 ≤ 1 + ε / 2) isOpen_Ioo hsub
  refine ⟨γ, hγ, (heq (by constructor <;> linarith)).trans hη0,
    (heq (by constructor <;> linarith)).trans hη1, ?_⟩
  intro t ht
  have hnear : γ =ᶠ[𝓝 t] η :=
    Filter.eventually_of_mem (Ioo_mem_nhds (by linarith [ht.1] : -ε / 2 < t)
      (by linarith [ht.2] : t < 1 + ε / 2))
        (fun _ hu => heq (Ioo_subset_Icc_self hu))
  change g.tangentNorm (γ t) (mfderiv 𝓘(ℝ) (𝓡 n) γ t 1) ≤ R
  rw [hnear.mfderiv_eq, hnear.self_of_nhds,
    hC t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  exact hCR.le

end PoincareConjecture.RiemannianMetric
