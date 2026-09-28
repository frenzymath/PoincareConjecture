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

theorem eventually_annular_distance_ascent_of_moving_centers
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
    {L : ℝ} (hL : 0 < L) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel ((g j).toBasedMetricSpace (p j))
        (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel ((g j).toBasedMetricSpace (p j))
      (L + δ j) (hpos j)).carrier)
    (u₀ : (ballModel Y L hL).carrier) (hu : S.PointConverges u u₀)
    {r R c c' : ℝ} (hr : 0 < r) (hR : 0 < R) (hcc' : c < c')
    (hroom : dist Y.base u₀.val + 2 * R < L)
    (hascent : ∀ y : Y.carrier, r ≤ dist u₀.val y → dist u₀.val y ≤ R →
      ∀ s : ℝ, 0 < s → ∃ q : Y.carrier, dist y q < s ∧
        c' * dist y q < dist u₀.val q - dist u₀.val y) :
    ∀ᶠ j in atTop, ∀ y : M j, r ≤ ((g j).edist (u j).val y).toReal →
      ((g j).edist (u j).val y).toReal ≤ R →
      ∀ s : ℝ, 0 < s → ∃ z : M j, ((g j).edist y z).toReal < s ∧
        c * ((g j).edist y z).toReal <
          ((g j).edist (u j).val z).toReal -
            ((g j).edist (u j).val y).toReal := by
  classical
  by_contra hfail
  let a := dist Y.base u₀.val
  let e := (L - a - 2 * R) / 4
  let ρ := a + e + R
  let σ := ρ + e
  have he : 0 < e := by dsimp [e, a]; linarith
  have hρσ : ρ < σ := by dsimp [σ]; linarith
  have hσL : σ < L := by dsimp [σ, ρ, e]; linarith
  let A : ℕ → FiniteDiameterBasedMetricSpace.{u} := fun j =>
    ballModel ((g j).toBasedMetricSpace (p j)) (L + δ j) (hpos j)
  let B : FiniteDiameterBasedMetricSpace.{u} := ballModel Y L hL
  have huBound : ∀ᶠ j in atTop, dist (A j).base (u j) < a + e :=
    (S.tendsto_dist_base u u₀ hu).eventually_lt_const (by change a < a + e; linarith)
  have hρL : ρ < L := hρσ.trans hσL
  have hrad : ∀ᶠ j in atTop, ρ < L + δ j := by
    have ht : Tendsto (fun j => L + δ j) atTop (𝓝 L) := by
      simpa using hδ.const_add L
    exact ht.eventually_const_lt hρL
  obtain ⟨φ, hφ, hφbad⟩ := Filter.extraction_of_frequently_atTop
    ((Filter.not_eventually.mp hfail).and_eventually (huBound.and hrad))
  have hbadpoint (j : ℕ) : ∃ y : M (φ j),
      r ≤ ((g (φ j)).edist (u (φ j)).val y).toReal ∧
      ((g (φ j)).edist (u (φ j)).val y).toReal ≤ R ∧
      ¬ (∀ s : ℝ, 0 < s → ∃ z : M (φ j), ((g (φ j)).edist y z).toReal < s ∧
        c * ((g (φ j)).edist y z).toReal <
          ((g (φ j)).edist (u (φ j)).val z).toReal -
            ((g (φ j)).edist (u (φ j)).val y).toReal) := by
    by_contra hnone
    apply (hφbad j).1
    intro y hry hyR
    by_contra hno
    exact hnone ⟨y, hry, hyR, hno⟩
  choose y hyr hyR hybad using hbadpoint
  have hybound (j : ℕ) : ((g (φ j)).edist (p (φ j)) (y j)).toReal ≤ ρ := by
    let := (g (φ j)).toMetricSpace
    have htri := dist_triangle (p (φ j)) (u (φ j)).val (y j)
    have hcenter : dist (p (φ j)) (u (φ j)).val < a + e := (hφbad j).2.1
    have houter : dist (u (φ j)).val (y j) ≤ R := hyR j
    change dist (p (φ j)) (y j) ≤ ρ
    dsimp only [ρ]
    linarith
  let x : ∀ j, (A (φ j)).carrier := fun j => ⟨y j, by
    let := (g (φ j)).toMetricSpace
    change dist (y j) (p (φ j)) < L + δ (φ j)
    rw [dist_comm]
    exact (hybound j).trans_lt (hφbad j).2.2⟩
  have hcompact : IsCompact (Metric.closedBall B.base σ) := by
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' Metric.closedBall B.base σ =
        Metric.closedBall Y.base σ := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, (show dist z Y.base ≤ σ from hz).trans_lt hσL⟩, hz, rfl⟩
    rw [heq]
    exact isCompact_closedBall Y.base σ
  let Sφ := S.comp φ hφ.tendsto_atTop
  obtain ⟨f, hf, y₀, _, ψ, hψ, hy₀⟩ :=
    exists_approximating_maps_and_subseq_pointConverges Sφ hρσ hcompact x hybound
  let Sψ := Sφ.comp ψ hψ.tendsto_atTop
  have hyconv : Sψ.PointConverges (fun j => x (ψ j)) y₀ := hy₀
  have huconv : Sψ.PointConverges (fun j => u (φ (ψ j))) u₀ :=
    (hu.comp φ hφ.tendsto_atTop).comp ψ hψ.tendsto_atTop
  have hdist := Sψ.tendsto_dist_of_pointConverges huconv hyconv
  have hylower : r ≤ dist u₀.val y₀.val :=
    ge_of_tendsto hdist (Eventually.of_forall (fun j => hyr (ψ j)))
  have hyupper : dist u₀.val y₀.val ≤ R :=
    le_of_tendsto hdist (Eventually.of_forall (fun j => hyR (ψ j)))
  obtain ⟨q, hql, hqaway, hqinc⟩ :=
    Poincare.Alexandrov.exists_distance_increment_witness_of_local_ascent
      (dist_pos.mp (hr.trans_le hylower)) K hcc' (hascent y₀.val hylower hyupper)
  have hqL : q ∈ Metric.ball Y.base L := by
    rw [Metric.mem_ball, dist_comm]
    have htri := dist_triangle Y.base u₀.val q
    have htri' := dist_triangle u₀.val y₀.val q
    linarith
  let q₀ : B.carrier := ⟨q, hqL⟩
  have hqconv : Sψ.PointConverges (fun j => f (ψ j) q₀) q₀ :=
    (hf q₀).comp ψ hψ.tendsto_atTop
  have hpq := Sψ.tendsto_dist_of_pointConverges huconv hqconv
  have hyq := Sψ.tendsto_dist_of_pointConverges hyconv hqconv
  have hevent := eventually_exists_arbitrarily_close_distance_ascent_of_tendsto
    (fun j => g (φ (ψ j))) (fun j => D (φ (ψ j))) (fun j => hc (φ (ψ j)))
    hK (fun j => hsec (φ (ψ j))) (fun j => (u (φ (ψ j))).val)
    (fun j => y (ψ j)) (fun j => (f (ψ j) q₀).val)
    hdist hyq hpq hql hqaway hqinc
  obtain ⟨j, hj⟩ := hevent.exists
  exact hybad (ψ j) hj

end PoincareConjecture.RiemannianMetric
