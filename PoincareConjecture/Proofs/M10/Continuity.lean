import PoincareConjecture.Proofs.M10.MinimizingLifts
import PoincareConjecture.Proofs.M10.CompactMinimum
import PoincareConjecture.Proofs.M10.UpperSemicontinuity










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem reducedLength_lowerSemicontinuousAt
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (z : M × ℝ) (hz : z ∈ Set.univ ×ˢ Set.Ioo 0 τmax) :
    LowerSemicontinuousAt (fun w : M × ℝ ↦ reducedLength F T p w.1 w.2) z := by
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡 n)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  let : ProperSpace (TangentSpace (𝓡 n) p) := FiniteDimensional.proper ℝ _
  obtain ⟨Q, hQcompact, hzQ, hQtime⟩ := exists_compact_subset
    (isOpen_univ.prod isOpen_Ioo) hz
  obtain ⟨A, _hA, hAmin⟩ := G.minimizing_initial_bounded Q hQcompact hQtime
  let I : Set ℝ := Prod.snd '' Q
  have hItime : I ⊆ Set.Ioo 0 τmax := by
    rintro s ⟨w, hw, rfl⟩
    exact (hQtime hw).2
  let K : Set (TangentSpace (𝓡 n) p × ℝ) := Metric.closedBall 0 A ×ˢ I
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : TangentSpace (𝓡 n) p) A).prod
      (hQcompact.image continuous_snd)
  have hKtime : K ⊆ Set.univ ×ˢ Set.Ioo 0 τmax :=
    fun _ hw ↦ ⟨Set.mem_univ _, hItime hw.2⟩
  let endpoint : TangentSpace (𝓡 n) p × ℝ → M × ℝ :=
    fun w ↦ (G.gamma w.1 w.2, w.2)
  let cost : TangentSpace (𝓡 n) p × ℝ → ℝ :=
    fun w ↦ G.toLExponentialFamily.action w.1 w.2 / (2 * Real.sqrt w.2)
  have hendpoint : ContinuousOn endpoint K :=
    (G.gamma_smooth.continuousOn.mono hKtime).prodMk continuous_snd.continuousOn
  have hcost : ContinuousOn cost K := by
    apply (G.action_smooth.continuousOn.mono hKtime).div
      (continuous_const.mul (Real.continuous_sqrt.comp continuous_snd)).continuousOn
    intro w hw
    exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hKtime hw).2.1).ne'
  apply lowerSemicontinuousAt_of_compact_lifts
    (mem_interior_iff_mem_nhds.mp hzQ) hK hendpoint hcost
  · intro w hw
    have hwtime := (hQtime hw).2
    obtain ⟨Z, hZend, hZmin, hZaction⟩ :=
      exists_minimizing_lift hL G w.1 w.2 hwtime.1 hwtime.2
    have hZbound : (F.metric T).tangentNorm p Z ≤ A :=
      hAmin Z w.2 hwtime.1 hwtime.2 (by simpa only [hZend] using hw) hZmin
    have hZnorm : ‖Z‖ ≤ A := by
      rw [norm_eq_sqrt_real_inner]
      exact hZbound
    refine ⟨(Z, w.2), ⟨?_, ⟨w, hw, rfl⟩⟩, ?_, hZaction.symm⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hZnorm
    · exact Prod.ext hZend rfl
  · intro w hw hwend
    have htime := (hKtime hw).2
    have hbound := reducedLength_le_normalized_action hL G w.1 w.2 htime.1 htime.2
    have hfirst : G.gamma w.1 w.2 = z.1 := congrArg Prod.fst hwend
    have hsecond : w.2 = z.2 := congrArg Prod.snd hwend
    change reducedLength F T p z.1 z.2 ≤
      G.toLExponentialFamily.action w.1 w.2 / (2 * Real.sqrt w.2)
    rw [hfirst, hsecond] at hbound
    simpa only [hsecond] using hbound


theorem reducedLength_continuousOn
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax) (p : M) :
    ContinuousOn (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2)
      (Set.univ ×ˢ Set.Ioo 0 τmax) := by
  obtain ⟨G⟩ := hDifferential.exponential_geometry p
  intro z hz
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_iff_lower_upperSemicontinuousAt.mpr
    ⟨reducedLength_lowerSemicontinuousAt hL G z hz,
      reducedLength_upperSemicontinuousAt hDifferential hz.2.1 hz.2.2⟩

end PoincareConjecture.M10
