import PoincareConjecture.Proofs.M09.SmoothSquarePath
import PoincareConjecture.Proofs.M09.ChartCurveExtension
import PoincareConjecture.Proofs.M09.SquareChartMetric

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def squareCurveActionDensity {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α : ℝ → M) (s : ℝ) : ℝ :=
  2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s) +
    (1 / 2 : ℝ) * regularizedCurveEnergy F T α s

noncomputable def squareChartActionDensity {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (z : (ℝ × E) × E) : ℝ :=
  2 * z.1.1 ^ 2 * squareChartScalar F T p z.1 +
    (1 / 2 : ℝ) * squareChartMetric F T p z.1 z.2 z.2

theorem squareCurveActionDensity_contDiffOn {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (α : ℝ → M) (D : Set ℝ) (hD : IsOpen D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (htime : D ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)) :
    ContDiffOn ℝ ∞ (squareCurveActionDensity F T α) D := by
  obtain ⟨hR, hE⟩ := smoothSquareCurve_scalar_energy F hM04 T τmax hτmax hwindow
    α D hD hα htime
  exact ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul hR).add (contDiffOn_const.mul hE)

set_option backward.isDefEq.respectTransparency false in
theorem squareCurveActionDensity_congr {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α β : ℝ → M) (s : ℝ) (heq : α =ᶠ[𝓝 s] β) :
    squareCurveActionDensity F T α s = squareCurveActionDensity F T β s := by
  have hb := heq.self_of_nhds
  have hv : (curveVelocity (n := n) α s : E) = curveVelocity (n := n) β s :=
    congrArg (fun L : ℝ →L[ℝ] E ↦ L 1)
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
  let Q : M → E → ℝ := fun q v ↦
    2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature q +
      (1 / 2 : ℝ) * (F.metric (T - s ^ 2)).inner q v v
  change Q (α s) (curveVelocity (n := n) α s) = Q (β s) (curveVelocity (n := n) β s)
  exact congrArg₂ Q hb hv

set_option backward.isDefEq.respectTransparency false in
theorem squareCurveActionDensity_inverseChart {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (a : ℝ → E) (s : ℝ) (v : E)
    (ha : HasDerivAt a v s) (hy : a s ∈ (chartAt E p).target) :
    squareCurveActionDensity F T (fun t ↦ (chartAt E p).symm (a t)) s =
      squareChartActionDensity F T p ((s, a s), v) := by
  have hv := curveVelocityWithin_inverseChart p a Set.univ s v
    uniqueDiffWithinAt_univ ha hy
  simp only [curveVelocityWithin, mfderivWithin_univ] at hv
  change 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature ((chartAt E p).symm (a s)) +
      (1 / 2 : ℝ) * (F.metric (T - s ^ 2)).inner ((chartAt E p).symm (a s))
        (curveVelocity (fun t ↦ (chartAt E p).symm (a t)) s)
        (curveVelocity (fun t ↦ (chartAt E p).symm (a t)) s) = _
  change curveVelocity (fun t ↦ (chartAt E p).symm (a t)) s = _ at hv
  rw [hv]
  rfl

theorem squareChartActionDensity_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (p : M) :
    ContDiffOn ℝ ∞ (squareChartActionDensity F T p)
      ((Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt E p).target) ×ˢ Set.univ) := by
  let S := (Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt E p).target) ×ˢ
    (Set.univ : Set E)
  have hG := (squareChartMetric_smooth F T τmax hτmax hwindow p).comp
    contDiffOn_fst (fun z (hz : z ∈ S) ↦ hz.1)
  have hR := (squareChartScalar_smooth F hM04 T τmax hτmax hwindow p).comp
    contDiffOn_fst (fun z (hz : z ∈ S) ↦ hz.1)
  have ht : ContDiffOn ℝ ∞ (fun z : (ℝ × E) × E ↦ z.1.1)
      ((Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt E p).target) ×ˢ Set.univ) :=
    (contDiff_fst.comp contDiff_fst).contDiffOn
  exact ((contDiffOn_const.mul (ht.pow 2)).mul hR).add
    (contDiffOn_const.mul ((hG.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd))

theorem squareChartActionDensity_bounded {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (p : M)
    (I : Set ℝ) (K : Set E) (hI : IsCompact I) (hK : IsCompact K)
    (hIt : I ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (hKt : K ⊆ (chartAt E p).target) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ I, ∀ y ∈ K, ∀ v : E, ‖v‖ ≤ R →
      |squareChartActionDensity F T p ((s, y), v)| ≤ C := by
  have hcompact := (hI.prod hK).prod (isCompact_closedBall (0 : E) R)
  have hsub : (I ×ˢ K) ×ˢ Metric.closedBall (0 : E) R ⊆
      (Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt E p).target) ×ˢ Set.univ :=
    fun z hz ↦ ⟨⟨hIt hz.1.1, hKt hz.1.2⟩, Set.mem_univ _⟩
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    ((squareChartActionDensity_contDiffOn F hM04 T τmax hτmax hwindow p).continuousOn.mono hsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs y hy v hv
  have hm : ((s, y), v) ∈ (I ×ˢ K) ×ˢ Metric.closedBall (0 : E) R :=
    ⟨⟨hs, hy⟩, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩
  exact (hC _ hm).trans (le_max_left _ _)

end PoincareConjecture.Proofs.M09
