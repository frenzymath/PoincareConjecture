import PoincareConjecture.Proofs.M10.ActionLowerBound
import PoincareConjecture.Proofs.M10.InitialActionLimit









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem reducedLength_range_bddBelow
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    BddBelow (range (fun q ↦ reducedLength F T p q τ)) := by
  obtain ⟨C, _, hC⟩ := exists_uniform_reducedLength_lower_bound hL G hcurvature
  refine ⟨-C * τ / 3, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact hC τ hτ hmax q


theorem sInf_reducedLength_tendsto_zero
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    Tendsto (fun τ : ℝ ↦ sInf (range (fun q ↦ reducedLength F T p q τ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_uniform_reducedLength_lower_bound hL G hcurvature
  let Z := metricCoordinates (F.metric T) p (0 : EuclideanSpace ℝ (Fin n))
  have hlo : Tendsto (fun τ : ℝ ↦ -C * τ / 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).const_mul
      (-C)).div_const 3).mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun τ : ℝ ↦ G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      normalized_action_tendsto_initial G hmax hT hwindow hcurvature 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [Ioo_mem_nhdsGT hmax] with τ hτ
    apply le_csInf ⟨reducedLength F T p p τ, mem_range_self p⟩
    rintro _ ⟨q, rfl⟩
    exact hC τ hτ.1 hτ.2 q
  · filter_upwards [Ioo_mem_nhdsGT hmax] with τ hτ
    exact (csInf_le (reducedLength_range_bddBelow hL G hcurvature hτ.1 hτ.2)
      (mem_range_self (G.gamma Z τ))).trans
        (reducedLength_le_normalized_action hL G Z τ hτ.1 hτ.2)

end PoincareConjecture.M10
