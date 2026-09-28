import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Busemann.Concavity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Busemann.StrictLevels
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem subsingleton_horoballIntersection_of_empty_interior
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (hpos : ∀ x : M, ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v)
    (p : M) (c : ℝ) (hempty : interior (horoballIntersection p c) = ∅) :
    (horoballIntersection p c).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨curve, hzero, hlast, hgeo, hspeed, hseg⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hcomplete x y
      (by rw [← hdist]; exact hd)
  rw [← hdist x y] at hlast hgeo hspeed hseg
  have hmem : MapsTo curve (Icc 0 (dist x y)) (horoballIntersection p c) := by
    apply mapsTo_horoballIntersection_of_concaveOn
      (fun ray hray _ => g.concaveOn_busemann_of_nonnegativeSectional
        D hcomplete hsec hdist hray hgeo)
    · simpa only [hzero] using hx
    · simpa only [hlast] using hy
  obtain ⟨r, hr, δ, hδ, hconc⟩ :=
    g.exists_uniform_concave_transformed_busemann D hcomplete hsec hdist
      (curve (dist x y / 2)) (hpos _) p
  let ε := min (r / 2) (dist x y / 4)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεr : ε ≤ r := (min_le_left _ _).trans (by linarith)
  have hεd : ε ≤ dist x y / 4 := min_le_right _ _
  have hsub : Icc (dist x y / 2 - ε) (dist x y / 2 + ε) ⊆ Icc 0 (dist x y) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmid : dist x y / 2 ∈ Icc (0 : ℝ) (dist x y) := by
    constructor <;> linarith
  have hnear : ∀ t ∈ Icc (dist x y / 2 - ε) (dist x y / 2 + ε),
      (g.edist (curve t) (curve (dist x y / 2))).toReal ≤ r := by
    intro t ht
    rw [hseg t (hsub ht) _ hmid, ENNReal.toReal_ofReal (abs_nonneg _)]
    apply le_trans _ hεr
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hunit : ∀ t ∈ Icc (dist x y / 2 - ε) (dist x y / 2 + ε),
      g.inner (curve t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1) = 1 := by
    intro t ht
    have hs := congrArg (fun z : ℝ => z ^ 2) (hspeed t (hsub ht))
    rw [tangentNorm, Real.sq_sqrt] at hs
    · simpa only [one_pow] using hs
    · by_cases hz : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1 = 0
      · simp [hz]
      · exact (g.pos _ _ hz).le
  have hab : dist x y / 2 - ε < dist x y / 2 + ε := by linarith
  have hinterior := midpoint_mem_interior_horoball_of_uniform_transformed_concavity
    hab hδ
    (hmem (hsub ⟨le_rfl, hab.le⟩)) (hmem (hsub ⟨hab.le, le_rfl⟩))
    (fun ray hray hray0 => hconc hray hray0 (fun t ht => hgeo t (hsub ht)) hnear hunit)
  rw [hempty] at hinterior
  exact hinterior

end PoincareConjecture.RiemannianMetric
