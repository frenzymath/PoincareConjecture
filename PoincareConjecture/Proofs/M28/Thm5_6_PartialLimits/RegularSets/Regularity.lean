import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.LocalNormalCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def regularPoints (g : RiemannianMetric n M) (δ : ℝ) : Set M :=
  {p | ∀ r : ℝ, r < δ → IsCompact (closure (g.ball p r))}

def regularComponent (g : RiemannianMetric n M) (p : M) (δ : ℝ) : Set M :=
  connectedComponentIn (regularPoints g δ) p

theorem regularPoints_antitone (g : RiemannianMetric n M) :
    Antitone (regularPoints g) := by
  intro δ ε hδε p hp r hr
  exact hp r (hr.trans_le hδε)

theorem regularComponent_antitone (g : RiemannianMetric n M) (p : M) :
    Antitone (regularComponent g p) := by
  intro δ ε hδε
  exact connectedComponentIn_mono p (regularPoints_antitone g hδε)

theorem regularComponent_subset (g : RiemannianMetric n M) (p : M) (δ : ℝ) :
    regularComponent g p δ ⊆ regularPoints g δ :=
  connectedComponentIn_subset _ _

theorem mem_regularComponent (g : RiemannianMetric n M) {p : M} {δ : ℝ}
    (hp : p ∈ regularPoints g δ) : p ∈ regularComponent g p δ :=
  mem_connectedComponentIn hp

theorem isPreconnected_regularComponent (g : RiemannianMetric n M) (p : M) (δ : ℝ) :
    IsPreconnected (regularComponent g p δ) :=
  isPreconnected_connectedComponentIn

theorem isConnected_regularComponent (g : RiemannianMetric n M) {p : M} {δ : ℝ}
    (hp : p ∈ regularPoints g δ) : IsConnected (regularComponent g p δ) :=
  isConnected_connectedComponentIn_iff.mpr hp

private theorem ball_eq_empty_of_nonpos (g : RiemannianMetric n M)
    (p : M) {r : ℝ} (hr : r ≤ 0) : g.ball p r = ∅ := by
  ext x
  simp [RiemannianMetric.ball, ENNReal.ofReal_eq_zero.mpr hr]

theorem mem_regularPoints_of_mem_ball (g : RiemannianMetric n M)
    {p q : M} {δ a : ℝ} (hp : p ∈ regularPoints g δ) (ha : 0 ≤ a)
    (hq : q ∈ g.ball p a) : q ∈ regularPoints g (δ - a) := by
  intro r hr
  by_cases hr0 : r ≤ 0
  · rw [ball_eq_empty_of_nonpos g q hr0, closure_empty]
    exact isCompact_empty
  · have hrpos : 0 < r := lt_of_not_ge hr0
    have hsub := riemannian_ball_subset_of_margin g ha hrpos.le hq
      (le_refl (a + r))
    exact (hp (a + r) (by linarith)).of_isClosed_subset isClosed_closure
      (closure_mono hsub)

theorem ball_subset_regularComponent (g : RiemannianMetric n M)
    {p q : M} {δ ε a : ℝ} (hq : q ∈ regularComponent g p δ)
    (ha : 0 < a) (hmargin : a + ε ≤ δ) :
    g.ball q a ⊆ regularComponent g p ε := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hqε : q ∈ regularComponent g p ε :=
    regularComponent_antitone g p (by linarith) hq
  have hqball : q ∈ g.ball q a := by
    change g.edist q q < ENNReal.ofReal a
    rw [show g.edist q q = 0 from Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr ha
  have hreg : g.ball q a ⊆ regularPoints g ε := by
    intro x hx
    apply regularPoints_antitone g (show ε ≤ δ - a by linarith)
    exact mem_regularPoints_of_mem_ball g (regularComponent_subset g p δ hq) ha.le hx
  have hsub := (g.isPreconnected_ball q a).subset_connectedComponentIn hqball hreg
  have heq := connectedComponentIn_eq hqε
  change g.ball q a ⊆ connectedComponentIn (regularPoints g ε) p
  rw [heq]
  exact hsub

theorem isClosed_regularPoints [T3Space M] (g : RiemannianMetric n M) (δ : ℝ) :
    IsClosed (regularPoints g δ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hball (q : M) (s : ℝ) : Metric.eball q (ENNReal.ofReal s) = g.ball q s := by
    ext x
    change g.edist x q < ENNReal.ofReal s ↔ g.edist q x < ENNReal.ofReal s
    rw [show g.edist x q = g.edist q x from Manifold.riemannianEDist_comm]
  apply closure_subset_iff_isClosed.mp
  intro p hp r hr
  by_cases hr0 : r ≤ 0
  · rw [ball_eq_empty_of_nonpos g p hr0, closure_empty]
    exact isCompact_empty
  · have hrpos : 0 < r := lt_of_not_ge hr0
    let a := (δ - r) / 4
    have ha : 0 < a := by dsimp [a]; linarith
    have hopen : IsOpen (g.ball p a) := by rw [← hball]; exact Metric.isOpen_eball
    have hmem : p ∈ g.ball p a := by
      rw [← hball]
      exact Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ha)
    obtain ⟨q, hq, hqreg⟩ := mem_closure_iff.mp hp (g.ball p a) hopen hmem
    have hpq : p ∈ g.ball q a := by
      change g.edist q p < ENNReal.ofReal a
      change g.edist p q < ENNReal.ofReal a at hq
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hq
    have hsub := riemannian_ball_subset_of_margin g ha.le hrpos.le hpq
      (show a + r ≤ r + 2 * a by linarith)
    exact (hqreg (r + 2 * a) (by dsimp [a]; linarith)).of_isClosed_subset
      isClosed_closure (closure_mono hsub)

theorem isClosed_regularComponent [T3Space M] (g : RiemannianMetric n M)
    (p : M) (δ : ℝ) : IsClosed (regularComponent g p δ) := by
  by_cases hp : p ∈ regularPoints g δ
  · apply closure_subset_iff_isClosed.mp
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hp))
      (closure_minimal (regularComponent_subset g p δ) (isClosed_regularPoints g δ))
  · change IsClosed (connectedComponentIn (regularPoints g δ) p)
    rw [connectedComponentIn_eq_empty hp]
    exact isClosed_empty

theorem closure_ball_subset_regularComponent [T3Space M] (g : RiemannianMetric n M)
    {p q : M} {δ ε a : ℝ} (hq : q ∈ regularComponent g p δ)
    (ha : 0 < a) (hmargin : a + ε ≤ δ) :
    closure (g.ball q a) ⊆ regularComponent g p ε :=
  closure_minimal (ball_subset_regularComponent g hq ha hmargin)
    (isClosed_regularComponent g p ε)

end PoincareConjecture.M28
