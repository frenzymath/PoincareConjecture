import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Increment
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Semiconcavity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_arbitrarily_close_distance_ascent_of_increment
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -K ≤ D.sectionalCurvature x v w)
    (p y q : M) (hl : 0 < (g.edist y q).toReal)
    (haway : (g.edist y q).toReal < (g.edist p y).toReal) {c : ℝ}
    (hinc : c < ((g.edist p q).toReal - (g.edist p y).toReal) /
      (g.edist y q).toReal -
        (4 / (3 * ((g.edist p y).toReal - (g.edist y q).toReal)) +
          K * ((g.edist p y).toReal + (g.edist y q).toReal) / 4) *
            (g.edist y q).toReal / 2) :
    ∀ s : ℝ, 0 < s → ∃ z : M, (g.edist y z).toReal < s ∧
      c * (g.edist y z).toReal < (g.edist p z).toReal - (g.edist p y).toReal := by
  let l := (g.edist y q).toReal
  let r := (g.edist p y).toReal - l
  let R := (g.edist p y).toReal + l
  let H := 4 / (3 * r) + K * R / 4
  have hr : 0 < r := sub_pos.mpr haway
  have hH : 0 ≤ H := by
    have hdpy := ENNReal.toReal_nonneg (a := g.edist p y)
    dsimp only [H, R]
    positivity
  obtain ⟨γ, hγ0, hγl, hγ, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc y q hl
  have hdist (t : ℝ) (ht : t ∈ Icc (0 : ℝ) l) : (g.edist y (γ t)).toReal = t := by
    have heq := congrArg ENNReal.toReal (hmin 0 ⟨le_rfl, hl.le⟩ t ht)
    simpa only [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1,
      ENNReal.toReal_ofReal ht.1] using heq
  have hannulus (t : ℝ) (ht : t ∈ Icc (0 : ℝ) l) :
      r ≤ (g.edist p (γ t)).toReal ∧ (g.edist p (γ t)).toReal ≤ R := by
    have hbound := abs_le.mp (g.abs_toReal_edist_sub_le p y (γ t))
    rw [hdist t ht] at hbound
    dsimp only [r, R]
    constructor <;> linarith [hbound.1, hbound.2, ht.2]
  have hconc : ConcaveOn ℝ (Icc 0 l)
      (fun t => (g.edist p (γ t)).toReal - H * t ^ 2 / 2) := by
    have h := g.distance_sub_quadratic_concave_of_annulus D hc hK hsec p
      hr hγ hspeed hannulus
    convert! h using 1
    funext t
    dsimp only [H]
    ring
  have hc' : c < ((g.edist p (γ l)).toReal - (g.edist p (γ 0)).toReal) / l -
      H * l / 2 := by
    rw [hγ0, hγl]
    exact hinc
  intro s hs
  let t := min s l / 2
  have ht : 0 < t := half_pos (lt_min hs hl)
  have hts : t < s := by
    dsimp only [t]
    linarith [min_le_left s l]
  have htl : t ≤ l := by
    dsimp only [t]
    linarith [min_le_right s l]
  refine ⟨γ t, ?_, ?_⟩
  · rw [hdist t ⟨ht.le, htl⟩]
    exact hts
  · rw [hdist t ⟨ht.le, htl⟩, ← hγ0]
    exact Poincare.Analysis.mul_lt_increment_of_concaveOn_sub_quadratic
      hl hH hconc hc' ht htl

end PoincareConjecture.RiemannianMetric
