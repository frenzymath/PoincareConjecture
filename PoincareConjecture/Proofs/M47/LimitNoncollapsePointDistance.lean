import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpTangent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.PathComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence S J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitNoncollapse_eventually_point_distance
    (t : ℝ) (ht : t ∈ J) (x y : G.limit.sliceCarrier.carrier)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop,
      t ∈ Icc (-G.exhaustion.time k) 0 ∧
      x ∈ G.exhaustion.space k ∧ y ∈ G.exhaustion.space k ∧
      ∀ hs : t ∈ Icc (-G.exhaustion.time k) 0,
        let h := (S.flow (G.subsequence k)).metric
          ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))
        let xk := (G.embedding k).forward t hs x
        let yk := (G.embedding k).forward t hs y
        h.edist xk yk ≠ ⊤ ∧
        Real.sqrt (S.scale (G.subsequence k)) * (h.edist xk yk).toReal <
          2 * (((G.limit.flow.metric t).edist x y).toReal + delta) := by
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let g := G.limit.flow.metric t
  let r := (g.edist x y).toReal + delta
  have hr : 0 < r := by dsimp only [r]; positivity
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : G.limit.carrier.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hxy : g.edist x y < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top x y)]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by dsimp [r]; linarith)
  obtain ⟨gamma, hg0, hg1, hgamma, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hxy zero_lt_one
  let K := gamma '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hgamma.continuous
  have hxK : x ∈ K := ⟨0, by norm_num, hg0⟩
  have hyK : y ∈ K := ⟨1, by norm_num, hg1⟩
  filter_upwards [limitNoncollapse_generalized_compact_tangent_comparison G hK t ht
    (lambda := 1 / 2) (by norm_num) (by norm_num)] with k hk
  refine ⟨hk.2.1, hk.1 hxK, hk.1 hyK, ?_⟩
  intro hs
  let f := (G.embedding k).forward t hs
  let h := (S.flow (G.subsequence k)).metric
    ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))
  let C := 2 / Real.sqrt (S.scale (G.subsequence k))
  have hroot : 0 < Real.sqrt (S.scale (G.subsequence k)) :=
    Real.sqrt_pos.mpr (G.embedding k).scale_pos
  have hC : 0 < C := div_pos two_pos hroot
  have hf : ∀ u ∈ Icc (0 : ℝ) 1, ContMDiffAt (𝓡 3) (𝓡 3) 1 f (gamma u) := by
    intro u hu
    have hgu := hk.1 (mem_image_of_mem gamma hu)
    exact ((G.embedding k).forward_smooth t hs (gamma u) hgu).contMDiffAt
      ((G.exhaustion.space_open k).mem_nhds hgu) |>.of_le (by simp)
  have hfactor : 1 / ((1 / 2) * Real.sqrt (S.scale (G.subsequence k))) = C := by
    dsimp [C]
    field_simp
  have hmapped : h.pathELength (f ∘ gamma) 0 1 ≤ ENNReal.ofReal C * g.pathELength gamma 0 1 :=
    g.pathELength_comp_le_of_tangentNorm_le_on_Icc h hC.le hgamma hf
      (fun u hu v => by
        simpa only [hfactor] using (hk.2.2 (gamma u) (mem_image_of_mem gamma hu) v hs).2)
  have hdist : h.edist (f x) (f y) ≤ h.pathELength (f ∘ gamma) 0 1 := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : ((S.flow (G.subsequence k)).slice
          ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).carrier → Type _) :=
      ⟨h.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength
      (fun u hu => ((hf u hu).comp u hgamma.contMDiffAt).contMDiffWithinAt)
      (by simp only [Function.comp_apply, hg0])
      (by simp only [Function.comp_apply, hg1]) zero_le_one
  have hstrict : h.edist (f x) (f y) < ENNReal.ofReal (C * r) := by
    rw [ENNReal.ofReal_mul hC.le]
    exact (hdist.trans hmapped).trans_lt
      (ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
        ENNReal.ofReal_ne_top hlength)
  refine ⟨ne_top_of_lt hstrict, ?_⟩
  have hrealdist := mul_lt_mul_of_pos_left (ENNReal.toReal_lt_of_lt_ofReal hstrict) hroot
  have hcancel : Real.sqrt (S.scale (G.subsequence k)) * (C * r) = 2 * r := by
    dsimp only [C]
    field_simp
  rwa [hcancel] at hrealdist

end PoincareConjecture.M47
