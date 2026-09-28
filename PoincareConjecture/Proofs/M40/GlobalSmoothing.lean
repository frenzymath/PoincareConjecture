import PoincareConjecture.Proofs.M40.RiemannianDistance
import PoincareConjecture.Proofs.M40.Mathlib.SmoothingCharts
import PoincareConjecture.Proofs.M40.Mathlib.FiniteSmoothingIteration
import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingPatch
import PoincareConjecture.Proofs.M40.MetricLocalToGlobal

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.M40

variable {M N : Type*}
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N] [PreconnectedSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

theorem exists_smooth_approximation
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f₀ : C(M, N))
    {L epsilon sigma : ℝ} (hL : 0 ≤ L) (hepsilon : 0 < epsilon) (hsigma : 0 < sigma)
    (hf₀ : ∀ x y, h.edist (f₀ x) (f₀ y) ≤ ENNReal.ofReal L * g.edist x y) :
    ∃ f : C(M, N), ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
      ContinuousMap.Homotopic f f₀ ∧
      (∀ x, h.edist (f x) (f₀ x) < ENNReal.ofReal epsilon) ∧
      (∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal (L + sigma) * g.edist x y) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : MetricSpace M := metricSpaceOfRiemannianMetric g
  let : MetricSpace N := metricSpaceOfRiemannianMetric h
  let : IsRiemannianManifold (𝓡 3) M := ⟨fun _ _ => rfl⟩
  let : IsRiemannianManifold (𝓡 3) N := ⟨fun _ _ => rfl⟩
  obtain ⟨n, c, rho, margin, hmargin, hsupp, hsmooth, hcover, hvalid⟩ :=
    exists_finite_smoothing_charts (E := EuclideanSpace ℝ (Fin 3))
      (F := EuclideanSpace ℝ (Fin 3)) f₀
  let tolerance : ℝ := min epsilon margin
  have htolerance : 0 < tolerance := lt_min hepsilon hmargin
  let W : Fin n → Set M := fun i => {x | (rho i : M → ℝ) =ᶠ[𝓝 x] 1}
  have hstep : ∀ (i : Fin n) (f : C(M, N)) (B : ℝ), 0 ≤ B →
      (∀ x, h.edist (f x) (f₀ x) < ENNReal.ofReal tolerance) →
      (∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal B * g.edist x y) →
      ∀ s e : ℝ, 0 < s → 0 < e →
        ∃ f' : C(M, N),
          (∀ x ∈ W i, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f' x) ∧
          (∀ x, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x →
            ContMDiffAt (𝓡 3) (𝓡 3) ∞ f' x) ∧
          ContinuousMap.Homotopic f' f ∧
          (∀ x, h.edist (f' x) (f x) < ENNReal.ofReal e) ∧
          (∀ x y, h.edist (f' x) (f' y) ≤ ENNReal.ofReal (B + s) * g.edist x y) := by
    intro i f B hB hclose hbound s e hs he
    have hcloseMargin : ∀ x, edist (f x) (f₀ x) < ENNReal.ofReal margin := fun x =>
      (hclose x).trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    have hLip : LipschitzWith ⟨B, hB⟩ f := by
      intro x y
      have hb := hbound x y
      change edist (f x) (f y) ≤ ENNReal.ofReal B * edist x y at hb
      rw [ENNReal.ofReal_eq_coe_nnreal hB] at hb
      exact hb
    obtain ⟨f', hnew, hpreserve, hhom, hmove, hlocal⟩ :=
      exists_supported_smooth_approximation volume
        (chartAt (EuclideanSpace ℝ (Fin 3)) (c i))
        (chartAt (EuclideanSpace ℝ (Fin 3)) (f₀ (c i)))
        contMDiffOn_chart contMDiffOn_chart_symm
        contMDiffOn_chart contMDiffOn_chart_symm (rho i) (hsmooth i)
        (fun _ => (rho i).mem_Icc)
        (isClosed_tsupport (rho i)).isCompact (hsupp i)
        f (hvalid f hcloseMargin i) ⟨B, hB⟩ hLip s e hs he
    refine ⟨f', hnew, hpreserve, hhom, ?_, ?_⟩
    · intro x
      change edist (f' x) (f x) < ENNReal.ofReal e
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff he).mpr (hmove x)
    · apply metric_edist_le_mul_of_local_pair_bound g h f' (by linarith)
      intro x
      obtain ⟨V, hV, hVLip⟩ := hlocal x
      refine ⟨V, hV, fun y hy z hz => ?_⟩
      change edist (f' y) (f' z) ≤ ENNReal.ofReal (B + s) * edist y z
      rw [ENNReal.ofReal_eq_coe_nnreal (add_nonneg hB hs.le)]
      exact hVLip hy hz
  obtain ⟨f, hf, hhom, hclose, hbound⟩ :=
    exists_smooth_of_finite_local_smoothing W hcover g.edist h.edist
      (fun y => by
        change edist y y = 0
        exact edist_self y) (fun x y z => by
        change edist x z ≤ edist x y + edist y z
        exact edist_triangle x y z)
      f₀ hL htolerance hsigma hf₀ hstep
  exact ⟨f, hf, hhom, fun x => (hclose x).trans_le
    (ENNReal.ofReal_le_ofReal (min_le_left _ _)), hbound⟩

end PoincareConjecture.M40
