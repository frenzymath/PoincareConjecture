import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EmbeddingInverse
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.RelativeCompactMetric
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.InverseOpenDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}

theorem eventually_edist_le_twice_captured_path_length
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ j : ℕ, ∀ᶠ k in atTop,
      ∀ x y : G.limitCarrier.carrier, x ∈ G.exhaustion k → y ∈ G.exhaustion k →
        ∀ (gamma : ℝ → M (G.subsequence k)) (a b : ℝ), a ≤ b →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc a b) →
          gamma a = G.embedding k x → gamma b = G.embedding k y →
          MapsTo gamma (Icc a b) (G.embedding k '' G.exhaustion j) →
          G.limitMetric.edist x y ≤
            2 * (g (G.subsequence k)).pathELength gamma a b := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro j
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun i => subset_closure.trans (G.exhaustion_step i))
  filter_upwards [G.eventually_compact_relative_inner_bounds
    (closure (G.exhaustion j)) (G.exhaustion_compactClosure j) 3 (by norm_num),
    eventually_ge_atTop j] with k hcompare hjk
  intro x y hx hy gamma a b hab hgamma h0 h1 hcapture
  let e := G.stageDiffeomorph k
  have hsource : G.exhaustion j ⊆ e.source := hmono hjk
  let U : TopologicalSpace.Opens (M (G.subsequence k)) :=
    ⟨e '' G.exhaustion j,
      e.toOpenPartialHomeomorph.isOpen_image_of_subset_source (G.exhaustion_open j) hsource⟩
  have hU : (U : Set (M (G.subsequence k))) ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.toPartialEquiv.map_source (hsource hz)
  have hbound : ∀ z ∈ (U : Set (M (G.subsequence k))),
      ∀ v : TangentSpace (𝓡 3) (e.symm z),
        G.limitMetric.inner (e.symm z) v v ≤ (2 : ℝ) ^ 2 *
          (g (G.subsequence k)).inner (e (e.symm z))
            (mfderiv (𝓡 3) (𝓡 3) e (e.symm z) v)
            (mfderiv (𝓡 3) (𝓡 3) e (e.symm z) v) := by
    rintro _ ⟨z, hz, rfl⟩
    have heq : e.symm.toPartialEquiv (e.toPartialEquiv z) = z :=
      e.toPartialEquiv.left_inv (hsource hz)
    rw [heq]
    intro v
    have hl := (hcompare z (subset_closure hz) v).1
    change G.limitMetric.inner z v v ≤ (2 : ℝ) ^ 2 *
      (g (G.subsequence k)).inner (G.embedding k z)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) z v)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) z v)
    norm_num at hl ⊢
    linarith only [hl]
  obtain ⟨eta, heta, heq, hlength⟩ :=
    exists_intrinsicOpenMetric_path_lift (g (G.subsequence k)) U hab hgamma hcapture
  have hleft : e.symm (eta a : M (G.subsequence k)) = x := by
    rw [show (eta a : M (G.subsequence k)) = e x from
      (heq (left_mem_Icc.mpr hab)).trans h0]
    exact e.toPartialEquiv.left_inv hx
  have hright : e.symm (eta b : M (G.subsequence k)) = y := by
    rw [show (eta b : M (G.subsequence k)) = e y from
      (heq (right_mem_Icc.mpr hab)).trans h1]
    exact e.toPartialEquiv.left_inv hy
  have hinverse := inverse_edist_le_intrinsicOpenMetric G.limitMetric
    (g (G.subsequence k)) e U hU (by norm_num : (0 : ℝ) < 2) hbound (eta a) (eta b)
  rw [hleft, hright, ENNReal.ofReal_ofNat] at hinverse
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨(intrinsicOpenMetric (g (G.subsequence k)) U).toRiemannianMetric⟩
  have hdist : (intrinsicOpenMetric (g (G.subsequence k)) U).edist (eta a) (eta b) ≤
      (intrinsicOpenMetric (g (G.subsequence k)) U).pathELength eta a b :=
    Manifold.riemannianEDist_le_pathELength heta rfl rfl hab
  exact hinverse.trans (mul_le_mul_right (hdist.trans_eq hlength) 2)

end PoincareConjecture.M28.RegularPointedMetricConvergence
