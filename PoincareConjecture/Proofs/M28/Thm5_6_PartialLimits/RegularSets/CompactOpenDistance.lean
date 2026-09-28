import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.RelativeCompactMetric
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.InverseOpenDistance









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}




theorem eventually_compact_open_edist_le (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (U : TopologicalSpace.Opens G.limitCarrier.carrier),
      IsCompact (closure (U : Set G.limitCarrier.carrier)) →
      ∀ c : ℝ, 1 < c → ∀ᶠ k in atTop, ∀ x y : U,
        (g (G.subsequence k)).edist (G.embedding k x) (G.embedding k y) ≤
          ENNReal.ofReal c * (intrinsicOpenMetric G.limitMetric U).edist x y := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro U hU c hc
  have hc0 : 0 < c := zero_lt_one.trans hc
  have htau : 0 < c ^ 2 - 1 := by nlinarith
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  obtain ⟨j, hj⟩ := hU.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) hmono.directed_le
  filter_upwards [G.eventually_compact_relative_inner_bounds _ hU _ htau,
    eventually_ge_atTop j] with k hk hjk
  let F : U → M (G.subsequence k) := G.embedding k ∘ Subtype.val
  have hstage (x : U) : (x : G.limitCarrier.carrier) ∈ G.exhaustion k :=
    hmono hjk (hj (subset_closure x.property))
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F := by
    intro x
    exact (G.embedding_smooth k ⟨x, hstage x⟩).contMDiffAt.comp x
      (contMDiff_subtype_val (I := 𝓡 3) (U := U)).contMDiffAt
  intro z w
  apply (intrinsicOpenMetric G.limitMetric U).edist_le_mul_of_inner_mfderiv_le
    (g (G.subsequence k)) (hF.of_le (by simp)) hc0 _ z w
  intro x v
  have hb := (hk x (subset_closure x.property)
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limitCarrier.carrier) x v)).2
  have hcomp := mfderiv_comp x
    ((G.embedding_smooth k ⟨x, hstage x⟩).contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓡 3) (U := U) (n := ∞)).mdifferentiable (by simp) x)
  have hv := congrArg (fun A => A v) hcomp
  change mfderiv (𝓡 3) (𝓡 3) F x v = _ at hv
  rw [hv, intrinsicOpenMetric_inner]
  rw [show 1 + (c ^ 2 - 1) = c ^ 2 by ring] at hb
  exact hb

end PoincareConjecture.M28.RegularPointedMetricConvergence
