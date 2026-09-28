import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothConvergence
import PoincareConjecture.Proofs.M36.ComparisonCovariantJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance intrinsicJetBilinearNormedGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance intrinsicJetBilinearNormedSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

theorem eventually_intrinsic_jet_error_bound
    {ι : Type*} {l : Filter ι} (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    {B : ι → E → Bilin} {U K : Set E}
    (h : CompactSmoothConvergenceOn B g.euclideanCoefficients l U)
    (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ bound : ℝ, bound < epsilon ∧ ∀ᶠ i in l, ∀ x ∈ K,
      singularMetricJetErrorSquared g D (fun y v => B i y (v 0) (v 1)) m x ≤ bound := by
  obtain ⟨C, hC, hbound⟩ := M36.exists_comparison_covariant_jet_bound g D hK m
  let rho := Real.sqrt (epsilon / (2 * C))
  have hrho : 0 < rho := Real.sqrt_pos.mpr (div_pos hepsilon (by positivity))
  have hrhosq : C * rho ^ 2 = epsilon / 2 := by
    rw [Real.sq_sqrt (le_of_lt (div_pos hepsilon (by positivity)))]
    field_simp
  obtain ⟨V, hV, hKV, hVU⟩ := exists_compact_between hK h.isOpen hKU
  have hs : ∀ᶠ i in l, ContDiffOn ℝ ∞ (B i) (interior V) := by
    filter_upwards [h.eventually_smooth V hV hVU] with i hi
    exact fun x hx => (hi x (interior_subset hx)).contDiffWithinAt
  have hjets : ∀ᶠ i in l, ∀ j : Fin (m + 1), ∀ x ∈ K,
      dist (iteratedFDeriv ℝ (j : ℕ) g.euclideanCoefficients x)
        (iteratedFDeriv ℝ (j : ℕ) (B i) x) < rho := by
    rw [eventually_all]
    intro j
    exact Metric.tendstoUniformlyOn_iff.mp (h.jets j K hK hKU) rho hrho
  refine ⟨epsilon / 2, half_lt_self hepsilon, ?_⟩
  filter_upwards [hs, hjets] with i his hij
  intro x hx
  rw [← hrhosq]
  apply hbound (interior V) isOpen_interior hKV (B i) his rho hrho.le x hx
  intro j hj
  have hb := his.contDiffAt (isOpen_interior.mem_nhds (hKV hx))
  have hg := g.contDiffAt_euclideanCoefficients x
  rw [iteratedFDeriv_sub_apply
    (hb.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top))]
  simpa only [dist_eq_norm, norm_sub_rev] using
    (hij ⟨j, Nat.lt_succ_of_le hj⟩ x hx).le

end PoincareConjecture.M44
