import PoincareConjecture.Proofs.M10.BarrierLipschitz
import PoincareConjecture.Proofs.M10.Continuity









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p q : M}


theorem reducedLength_time_lipschitzOnWith
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    {S : Set ℝ} (hS : Convex ℝ S) (hStime : S ⊆ Set.Ioo 0 τmax)
    {C : ℝ≥0}
    (hbarrier : ∀ s ∈ S, ∃ B : ReducedLengthUpperBarrier F T p q s,
      |deriv (fun t ↦ B.representative (q, t)) s| ≤ C) :
    LipschitzOnWith C (fun s ↦ reducedLength F T p q s) S := by
  have hf : ContinuousOn (fun s ↦ reducedLength F T p q s) S :=
    (reducedLength_continuousOn hL hDifferential p).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hs ↦ ⟨Set.mem_univ _, hStime hs⟩)
  apply lipschitzOnWith_of_upper_supports hS hf
  intro s hs
  obtain ⟨B, hB⟩ := hbarrier s hs
  obtain ⟨d, hd⟩ := B.representative_time_derivative
  have hdom : ∀ᶠ z : M × ℝ in 𝓝 (q, s),
      reducedLength F T p z.1 z.2 ≤ B.representative z :=
    Filter.eventually_of_mem (B.neighborhood_open.mem_nhds B.center_mem) B.dominates
  refine ⟨fun t ↦ B.representative (q, t),
    ContinuousLinearMap.toSpanSingleton ℝ d, hd.hasFDerivAt, B.touches,
    (continuous_const.prodMk continuous_id).continuousAt hdom, ?_⟩
  simpa only [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs, hd.deriv] using hB


theorem reducedLength_local_time_lipschitz
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (z : M × ℝ) (hz : z ∈ Set.univ ×ˢ Set.Ioo 0 τmax) :
    ∃ N : Set (M × ℝ), IsOpen N ∧ z ∈ N ∧
      N ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧ ∃ C : ℝ≥0,
        ∀ q : M, ∀ a b : ℝ, a ≤ b →
          (∀ s ∈ Set.Icc a b, (q, s) ∈ N) →
          |reducedLength F T p q b - reducedLength F T p q a| ≤ C * |b - a| := by
  obtain ⟨N, hNopen, hzN, hNtime, C, hC, hbounds⟩ :=
    hDifferential.local_upper_barrier_bounds p z hz
  refine ⟨N, hNopen, hzN, hNtime, ⟨C, hC⟩, ?_⟩
  intro q a b hab hsegment
  have htime : Set.Icc a b ⊆ Set.Ioo 0 τmax :=
    fun s hs ↦ (hNtime (hsegment s hs)).2
  have hLip := reducedLength_time_lipschitzOnWith hL hDifferential
    (p := p) (q := q) (convex_Icc a b) htime (C := ⟨C, hC⟩) (fun s hs ↦ ?_)
  · simpa only [Real.dist_eq] using hLip.dist_le_mul b ⟨hab, le_rfl⟩ a ⟨le_rfl, hab⟩
  obtain ⟨B, hB, _⟩ := hbounds (q, s) (hsegment s hs)
  exact ⟨B, hB⟩

end PoincareConjecture.M10
