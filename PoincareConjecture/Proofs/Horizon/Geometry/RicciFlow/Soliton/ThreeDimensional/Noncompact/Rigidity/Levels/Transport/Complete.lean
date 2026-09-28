import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Complete.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Speed
import Mathlib.Analysis.SpecialFunctions.SmoothTransition









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_complete_flow_of_bounded_speed (g : RiemannianMetric n M)
    (hc : MetricComplete g) (X : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, g.tangentNorm x (X x) ≤ B) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) := by
  apply Poincare.Manifold.exists_smooth_globalFlow_of_compact_confinement hX
  intro x A hA
  refine ⟨{y | g.edist x y ≤ ENNReal.ofReal (A * B)},
    g.isCompact_closedBall_of_metricComplete hc x (A * B), ?_⟩
  intro a ha haA γ h0 hγ horbit t ht
  have hz : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hspeed (s : ℝ) (hs : s ∈ Ioo (-a) a) :
      g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ B := by
    rw [(horbit.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hs)).hasMFDerivAt.mfderiv]
    change g.tangentNorm (γ s) ((1 : ℝ) • X (γ s)) ≤ B
    simpa only [one_smul] using hbound (γ s)
  change g.edist x (γ t) ≤ ENNReal.ofReal (A * B)
  rw [← h0]
  rcases le_total 0 t with ht0 | ht0
  · have hsub : Icc 0 t ⊆ Ioo (-a) a := fun s hs =>
      ⟨hz.1.trans_le hs.1, hs.2.trans_lt ht.2⟩
    apply (g.edist_le_of_speed_le_on_Icc isOpen_Ioo hγ ht0 hsub
      (fun s hs => hspeed s (hsub hs))).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [ht.2.trans_le haA]
  · have hsub : Icc t 0 ⊆ Ioo (-a) a := fun s hs =>
      ⟨ht.1.trans_le hs.1, hs.2.trans_lt hz.2⟩
    have hsym : g.edist (γ 0) (γ t) = g.edist (γ t) (γ 0) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_comm
    rw [hsym]
    apply (g.edist_le_of_speed_le_on_Icc isOpen_Ioo hγ ht0 hsub
      (fun s hs => hspeed s (hsub hs))).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [ht.1]

end PoincareConjecture.RiemannianMetric
