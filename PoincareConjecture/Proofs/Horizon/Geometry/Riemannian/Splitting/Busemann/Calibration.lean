import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem exists_busemann_calibrated_point (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (x : M) {r : ℝ} (hr : 0 < r) :
    ∃ y : M, g.edist x y = ENNReal.ofReal r ∧
      g.busemann γ y = g.busemann γ x + r := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm (p q : M) : g.edist p q = g.edist q p := Manifold.riemannianEDist_comm
  let K : Set M := {y | g.edist x y ≤ ENNReal.ofReal r}
  have hK : IsCompact K := g.isCompact_closedBall_of_metricComplete hcomplete x r
  have hxK : x ∈ K := by
    simp only [K, mem_ofPred_eq, edist, Manifold.riemannianEDist_self]
    exact zero_le
  obtain ⟨y, hyK, hymax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩
    (g.continuous_busemann hγ).continuousOn
  have hdle : (g.edist x y).toReal ≤ r := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hyK
    simpa only [ENNReal.toReal_ofReal hr.le] using h
  have hupper : g.busemann γ y ≤ g.busemann γ x + r := by
    have hlip := (abs_le.mp (g.abs_busemann_sub_le hγ x y)).1
    linarith
  have hlower : g.busemann γ x + r ≤ g.busemann γ y := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hlim : ∀ᶠ t : ℝ in atTop,
        g.busemann γ x - ε / 2 < g.busemannApprox γ t x :=
      (tendsto_order.mp (g.tendsto_busemannApprox hγ x)).1 _ (by linarith)
    obtain ⟨t, htlim, htfar⟩ :=
      (hlim.and (eventually_gt_atTop (r + (g.edist (γ 0) x).toReal))).exists
    have ht : 0 < t := by linarith [ENNReal.toReal_nonneg (a := g.edist (γ 0) x)]
    have hfar : r < (g.edist x (γ t)).toReal := by
      have htri := g.toReal_edist_triangle (γ 0) x (γ t)
      rw [hγ, zero_sub, abs_neg, abs_of_pos ht, ENNReal.toReal_ofReal ht.le] at htri
      linarith
    obtain ⟨z, hz, _, hzrest⟩ := g.exists_approximate_distance_split
      x (γ t) (g.edist_ne_top x (γ t)) hr (by linarith : 0 < ε / 2) hfar
    have hzK : z ∈ K := hz.le
    have hzmax : g.busemann γ z ≤ g.busemann γ y := hymax hzK
    have hzapprox := g.busemannApprox_le_busemann hγ ht.le z
    rw [hcomm z (γ t), hcomm x (γ t)] at hzrest
    dsimp [busemannApprox] at htlim hzapprox
    linarith
  have heq := le_antisymm hupper hlower
  refine ⟨y, ?_, heq⟩
  have hdeq : (g.edist x y).toReal = r := by
    have hlip := (abs_le.mp (g.abs_busemann_sub_le hγ x y)).1
    rw [heq] at hlip
    linarith
  rw [← ENNReal.ofReal_toReal (g.edist_ne_top x y), hdeq]

end PoincareConjecture.RiemannianMetric
