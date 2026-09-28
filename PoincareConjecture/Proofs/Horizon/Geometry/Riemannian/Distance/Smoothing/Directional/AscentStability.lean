import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.AscentWitness
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.AscentWitness


set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric



theorem eventually_exists_arbitrarily_close_distance_ascent_of_tendsto
    {n : ℕ} {M : ℕ → Type*} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (hc : ∀ j, MetricComplete (g j)) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -K ≤ (D j).sectionalCurvature x v w)
    (p y q : ∀ j, M j) {a l d c : ℝ}
    (ha : Tendsto (fun j => ((g j).edist (p j) (y j)).toReal) atTop (𝓝 a))
    (hl : Tendsto (fun j => ((g j).edist (y j) (q j)).toReal) atTop (𝓝 l))
    (hd : Tendsto (fun j => ((g j).edist (p j) (q j)).toReal) atTop (𝓝 d))
    (hl0 : 0 < l) (haway : l < a)
    (hinc : c < (d - a) / l - (4 / (3 * (a - l)) + K * (a + l) / 4) * l / 2) :
    ∀ᶠ j in atTop, ∀ s : ℝ, 0 < s → ∃ z : M j,
      ((g j).edist (y j) z).toReal < s ∧
        c * ((g j).edist (y j) z).toReal <
          ((g j).edist (p j) z).toReal - ((g j).edist (p j) (y j)).toReal := by
  have hden : (3 : ℝ) * (a - l) ≠ 0 := by positivity
  have hH : Tendsto
      (fun j => 4 / (3 * (((g j).edist (p j) (y j)).toReal -
          ((g j).edist (y j) (q j)).toReal)) +
        K * (((g j).edist (p j) (y j)).toReal +
          ((g j).edist (y j) (q j)).toReal) / 4)
      atTop (𝓝 (4 / (3 * (a - l)) + K * (a + l) / 4)) :=
    (tendsto_const_nhds.div ((ha.sub hl).const_mul 3) hden).add
      (((ha.add hl).const_mul K).div_const 4)
  have hmargin : Tendsto
      (fun j => (((g j).edist (p j) (q j)).toReal -
          ((g j).edist (p j) (y j)).toReal) / ((g j).edist (y j) (q j)).toReal -
        (4 / (3 * (((g j).edist (p j) (y j)).toReal -
            ((g j).edist (y j) (q j)).toReal)) +
          K * (((g j).edist (p j) (y j)).toReal +
            ((g j).edist (y j) (q j)).toReal) / 4) *
              ((g j).edist (y j) (q j)).toReal / 2)
      atTop (𝓝 ((d - a) / l - (4 / (3 * (a - l)) + K * (a + l) / 4) * l / 2)) :=
    ((hd.sub ha).div hl hl0.ne').sub ((hH.mul hl).div_const 2)
  filter_upwards [hl.eventually (lt_mem_nhds hl0),
    (ha.sub hl).eventually (lt_mem_nhds (sub_pos.mpr haway)),
    hmargin.eventually (lt_mem_nhds hinc)] with j hlj hawayj hincj
  let : ConnectedSpace (M j) := { toNonempty := ⟨p j⟩ }
  exact (g j).exists_arbitrarily_close_distance_ascent_of_increment
    (D j) (hc j) hK (hsec j) (p j) (y j) (q j) hlj (sub_pos.mp hawayj) hincj



theorem eventually_exists_arbitrarily_close_distance_ascent_of_local_ascent
    {X : Type*} [MetricSpace X] {n : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (D : ∀ j, LeviCivitaData (g j))
    (hc : ∀ j, MetricComplete (g j)) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -K ≤ (D j).sectionalCurvature x v w)
    {p y : X} (hpy : p ≠ y) (pj yj : ∀ j, M j) (f : ∀ j, X → M j)
    (hpyj : Tendsto (fun j => ((g j).edist (pj j) (yj j)).toReal)
      atTop (𝓝 (dist p y)))
    (hp : ∀ q : X, Tendsto (fun j => ((g j).edist (pj j) (f j q)).toReal)
      atTop (𝓝 (dist p q)))
    (hy : ∀ q : X, Tendsto (fun j => ((g j).edist (yj j) (f j q)).toReal)
      atTop (𝓝 (dist y q)))
    {c c' : ℝ} (hcc' : c < c')
    (hascent : ∀ s : ℝ, 0 < s → ∃ q : X, dist y q < s ∧
      c' * dist y q < dist p q - dist p y) :
    ∀ᶠ j in atTop, ∀ s : ℝ, 0 < s → ∃ z : M j,
      ((g j).edist (yj j) z).toReal < s ∧
        c * ((g j).edist (yj j) z).toReal <
          ((g j).edist (pj j) z).toReal - ((g j).edist (pj j) (yj j)).toReal := by
  obtain ⟨q, hqpos, hqaway, hqinc⟩ :=
    Poincare.Alexandrov.exists_distance_increment_witness_of_local_ascent hpy K hcc' hascent
  exact eventually_exists_arbitrarily_close_distance_ascent_of_tendsto g D hc hK hsec
    pj yj (fun j => f j q) hpyj (hy q) (hp q) hqpos hqaway hqinc

end PoincareConjecture.RiemannianMetric
