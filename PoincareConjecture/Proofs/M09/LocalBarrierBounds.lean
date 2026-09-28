import PoincareConjecture.Proofs.M09.MinimizingBarrierBounds
import PoincareConjecture.Proofs.M09.CompactMinimizingPreimages








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_local_upper_barrier_bounds {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p)
    (z : M × ℝ) (hz : z ∈ Set.univ ×ˢ Set.Ioo 0 τmax) :
    ∃ N : Set (M × ℝ), IsOpen N ∧ z ∈ N ∧ N ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ N,
        ∃ B : ReducedLengthUpperBarrier F T p w.1 w.2,
          |deriv (fun s ↦ B.representative (w.1, s)) w.2| ≤ C ∧
          reducedLengthGradientNormSq F T B.representative w.2 w.1 ≤ C ∧
          ∀ v : TangentSpace (𝓡 n) w.1,
            (F.connection (T - w.2)).hessian (fun q ↦ B.representative (q, w.2)) w.1 v v ≤
              C * (F.metric (T - w.2)).inner w.1 v v := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨Q, hQnear, hQt, hQ⟩ := local_compact_nhds
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  let S := {a : TangentSpace (𝓡 n) p × ℝ |
    ∃ (ht : 0 < a.2) (hm : a.2 < τmax), (A.gamma a.1 a.2, a.2) ∈ Q ∧
      IsMinimizingBackwardLPath F T 0 a.2 (A.path a.1 a.2 ht hm)}
  have hS : IsCompact S := lExponentialFamily_isCompact_minimizing_preimage F hM04 T τmax
    hτmax hwindow hcurvature hL p A Q hQ hQt
  have htime (a : S) : 0 < a.val.2 ∧ a.val.2 < τmax := by
    obtain ⟨ht, hm, _⟩ := a.property
    exact ⟨ht, hm⟩
  choose U hU haU hUt D hD hbound using fun a : S ↦
    lExponentialFamily_local_minimizing_barrier_bounds hM04 hL hτmax hwindow A
      a.val.1 a.val.2 (htime a).1 (htime a).2
  obtain ⟨K, hK⟩ := hS.elim_finite_subcover U hU (by
    intro a ha
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, haU ⟨a, ha⟩⟩)
  let C := ∑ a ∈ K, D a
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ ↦ hD a)
  have hDC (a : S) (ha : a ∈ K) : D a ≤ C :=
    Finset.single_le_sum (fun b _ ↦ hD b) ha
  refine ⟨interior Q, isOpen_interior, mem_interior_iff_mem_nhds.mpr hQnear,
    fun w hw ↦ hQt (interior_subset hw), C, hC, ?_⟩
  intro w hw
  have hwt := (hQt (interior_subset hw)).2
  obtain ⟨Z, hZ, hmin⟩ := lExponentialFamily_exists_minimizing_initialVector hM04 hL
    hτmax hwindow A w.2 hwt.1 hwt.2 w.1
  have hZS : (Z, w.2) ∈ S := ⟨hwt.1, hwt.2, by
    change (A.gamma Z w.2, w.2) ∈ Q
    rw [hZ]
    exact interior_subset hw, hmin⟩
  obtain ⟨a, haK, hUa⟩ := Set.mem_iUnion₂.mp (hK hZS)
  obtain ⟨B, hBt, hBg, hBh⟩ := hbound a (Z, w.2) hUa hwt.1 hwt.2 hmin
  have hBd : ∃ B : ReducedLengthUpperBarrier F T p w.1 w.2,
      |deriv (fun s ↦ B.representative (w.1, s)) w.2| ≤ D a ∧
      reducedLengthGradientNormSq F T B.representative w.2 w.1 ≤ D a ∧
      ∀ v : TangentSpace (𝓡 n) w.1,
        (F.connection (T - w.2)).hessian (fun q ↦ B.representative (q, w.2)) w.1 v v ≤
          D a * (F.metric (T - w.2)).inner w.1 v v := by
    rw [← hZ]
    exact ⟨B, hBt, hBg, hBh⟩
  obtain ⟨B, hBt, hBg, hBh⟩ := hBd
  refine ⟨B, hBt.trans (hDC a haK), hBg.trans (hDC a haK), ?_⟩
  intro v
  have hv : 0 ≤ (F.metric (T - w.2)).inner w.1 v v := by
    rcases eq_or_ne v 0 with rfl | hne
    · simp
    · exact ((F.metric (T - w.2)).pos w.1 v hne).le
  exact (hBh v).trans (mul_le_mul_of_nonneg_right (hDC a haK) hv)

end PoincareConjecture.Proofs.M09
