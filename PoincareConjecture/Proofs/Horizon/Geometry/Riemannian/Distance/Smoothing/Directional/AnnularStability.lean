import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.AscentStability
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.Packing
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

theorem eventually_annular_distance_ascent_of_pointedGHConvergesUnbounded
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j)) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -K ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y)
    {r R c c' : ℝ} (hr : 0 < r) (hcc' : c < c')
    (hascent : ∀ y : Y.carrier, r ≤ dist Y.base y → dist Y.base y ≤ R →
      ∀ s : ℝ, 0 < s → ∃ q : Y.carrier, dist y q < s ∧
        c' * dist y q < dist Y.base q - dist Y.base y) :
    ∀ᶠ j in atTop, ∀ y : M j, r ≤ ((g j).edist (p j) y).toReal →
      ((g j).edist (p j) y).toReal ≤ R →
      ∀ s : ℝ, 0 < s → ∃ z : M j, ((g j).edist y z).toReal < s ∧
        c * ((g j).edist y z).toReal <
          ((g j).edist (p j) z).toReal - ((g j).edist (p j) y).toReal := by
  classical
  by_contra hfail
  have hbad := Filter.not_eventually.mp hfail
  let ρ : ℝ := max R 1
  have hρ : 0 < ρ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRρ : R ≤ ρ := le_max_left _ _
  let L : ℝ := 3 * ρ
  have hL : 0 < L := by dsimp [L]; positivity
  have hRL : R < L := by dsimp [L]; linarith
  obtain ⟨δ, hδ, hpos, hballs⟩ := hconv L hL
  have hroom : ∀ᶠ j in atTop, R < L + δ j := by
    have ht : Tendsto (fun j => L + δ j) atTop (𝓝 L) := by
      simpa using hδ.const_add L
    exact ht.eventually_const_lt hRL
  obtain ⟨φ, hφ, hφbad⟩ := Filter.extraction_of_frequently_atTop (hbad.and_eventually hroom)
  have hbadpoint (j : ℕ) : ∃ y : M (φ j),
      r ≤ ((g (φ j)).edist (p (φ j)) y).toReal ∧
      ((g (φ j)).edist (p (φ j)) y).toReal ≤ R ∧
      ¬ (∀ s : ℝ, 0 < s → ∃ z : M (φ j), ((g (φ j)).edist y z).toReal < s ∧
        c * ((g (φ j)).edist y z).toReal <
          ((g (φ j)).edist (p (φ j)) z).toReal -
            ((g (φ j)).edist (p (φ j)) y).toReal) := by
    by_contra hnone
    apply (hφbad j).1
    intro y hry hyR
    by_contra hno
    exact hnone ⟨y, hry, hyR, hno⟩
  choose y hyr hyR hybad using hbadpoint
  let A : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
    ballModel ((g j).toBasedMetricSpace (p j)) (L + δ j) (hpos j)
  let B : FiniteDiameterBasedMetricSpace.{u} := ballModel Y L hL
  let S := realizationSequenceOfPointedGHConverges A B hballs
  let Sφ := S.comp φ hφ.tendsto_atTop
  let x : ∀ j, (A (φ j)).carrier := fun j =>
    ⟨y j, by
      let := (g (φ j)).toMetricSpace
      change dist (y j) (p (φ j)) < L + δ (φ j)
      rw [dist_comm]
      exact (hyR j).trans_lt (hφbad j).2⟩
  have hx (j : ℕ) : dist (A (φ j)).base (x j) ≤ ρ := (hyR j).trans hRρ
  have hcompact : IsCompact (Metric.closedBall B.base (2 * ρ)) := by
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' Metric.closedBall B.base (2 * ρ) =
        Metric.closedBall Y.base (2 * ρ) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        have hzL : z ∈ Metric.ball Y.base L := by
          change dist z Y.base < L
          have hzd : dist z Y.base ≤ 2 * ρ := hz
          dsimp only [L]
          linarith
        exact ⟨⟨z, hzL⟩, hz, rfl⟩
    rw [heq]
    exact isCompact_closedBall Y.base (2 * ρ)
  obtain ⟨f, hf, y₀, _, ψ, hψ, hy₀⟩ :=
    exists_approximating_maps_and_subseq_pointConverges Sφ
      (show ρ < 2 * ρ by linarith) hcompact x hx
  let Sψ := Sφ.comp ψ hψ.tendsto_atTop
  have hyconv : Sψ.PointConverges (fun j => x (ψ j)) y₀ := hy₀
  have hrad := Sψ.tendsto_dist_base (fun j => x (ψ j)) y₀ hyconv
  have hylower : r ≤ dist Y.base y₀.val :=
    ge_of_tendsto hrad (Eventually.of_forall (fun j => hyr (ψ j)))
  have hyupper : dist Y.base y₀.val ≤ R :=
    le_of_tendsto hrad (Eventually.of_forall (fun j => hyR (ψ j)))
  have hpyn : Y.base ≠ y₀.val := dist_pos.mp (hr.trans_le hylower)
  obtain ⟨q, hql, hqaway, hqinc⟩ :=
    Poincare.Alexandrov.exists_distance_increment_witness_of_local_ascent hpyn K hcc'
      (hascent y₀.val hylower hyupper)
  have hqL : q ∈ Metric.ball Y.base L := by
    rw [Metric.mem_ball, dist_comm]
    have htri := dist_triangle Y.base y₀.val q
    dsimp only [L]
    linarith
  let q₀ : B.carrier := ⟨q, hqL⟩
  have hqconv : Sψ.PointConverges (fun j => f (ψ j) q₀) q₀ :=
    (hf q₀).comp ψ hψ.tendsto_atTop
  have hpq := Sψ.tendsto_dist_base (fun j => f (ψ j) q₀) q₀ hqconv
  have hyq := Sψ.tendsto_dist_of_pointConverges hyconv hqconv
  have hevent := eventually_exists_arbitrarily_close_distance_ascent_of_tendsto
    (fun j => g (φ (ψ j))) (fun j => D (φ (ψ j))) (fun j => hc (φ (ψ j)))
    hK (fun j => hsec (φ (ψ j))) (fun j => p (φ (ψ j)))
    (fun j => y (ψ j)) (fun j => (f (ψ j) q₀).val)
    hrad hyq hpq hql hqaway hqinc
  obtain ⟨j, hj⟩ := hevent.exists
  exact hybad (ψ j) hj

end PoincareConjecture.RiemannianMetric
