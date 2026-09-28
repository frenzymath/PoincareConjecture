import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierTangent
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCapture










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem terminalCurvature_source_balls_of_original_jets
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T3Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (hcomplete : MetricComplete h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ 0 ((g k).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ 0 (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) {R : ℝ} (hR : 0 < R) :
    ∃ j, ∀ᶠ k in atTop, (g k).ball (phi k x) R ⊆ phi k '' U j := by
  let K : Set X := {z | h.edist x z ≤ ENNReal.ofReal (4 * R + 1)}
  have hK : IsCompact K :=
    h.isCompact_closedBall_of_metricComplete hcomplete x (4 * R + 1)
  have htangent := terminalCurvature_eventually_compact_tangent
    g h U hU hmono hcover phi hsource c hcoverC hjet K hK
  have hclosed := terminalCommonInterval_compact_ball_closure h hcomplete x (2 * R)
  obtain ⟨j, hj⟩ := hclosed.elim_directed_cover U hU
    (by rw [hcover]; exact subset_univ _) hmono.directed_le
  refine ⟨j, ?_⟩
  filter_upwards [htangent] with k hk
  have hsourceK : K ⊆ (phi k).source := by rw [hsource k]; exact hk.1
  have hcapture := terminalCommonInterval_capture_of_closed_buffer
    h (g k) hcomplete (phi k).toOpenPartialHomeomorph
    ((phi k).contMDiffOn_toFun.of_le (by simp))
    ((phi k).contMDiffOn_invFun.of_le (by simp)) x
    (R := 4 * R + 1) (r := R) (C := 2)
    (by linarith) (by norm_num) (by linarith) hsourceK
    (fun z hz v => hk.2 z hz v)
  exact hcapture.trans (image_mono (subset_closure.trans hj))

end PoincareConjecture.M47
