import PoincareLib.Geometry.Riemannian.Soul.Separation.DistanceMaximum
import PoincareLib.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareLib.Topology.Connected.BoundaryIncidence

/-!
# Boundary diameter bounds the depth of a region omitting the soul

A minimizing segment from the soul to an interior point meets the frontier.
The radial distance maximum principle and the frontier diameter bound then
bound the remaining segment length. This is the metric obstruction used to
identify the bounded side of a sufficiently long neck.

Reference: Morgan--Tian, Lemma 2.20 and Proposition 2.19, pp. 31--32.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.RiemannianMetric.RadialHomeomorph

variable {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {p : M}

/-- If an open region has compact closure and omits the radial center, every
interior point is within the diameter of its frontier of a frontier point. -/
theorem exists_frontier_distance_le_diameter
    (H : RadialHomeomorph g p) (hc : MetricComplete g) {A : Set M}
    (hA : IsOpen A) (hcompact : IsCompact (closure A)) (hp : p ∉ A)
    {D : ℝ} (hdiam : ∀ y ∈ frontier A, ∀ z ∈ frontier A,
      (g.edist y z).toReal ≤ D) {x : M} (hx : x ∈ A) :
    ∃ y ∈ frontier A, (g.edist x y).toReal ≤ D := by
  obtain ⟨z, hz, hmax⟩ := H.exists_distance_le_frontier hcompact
    (fun h => hp (interior_subset h)) (subset_closure hx)
  obtain ⟨ε, hε, γ, hgeo, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p x
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ (hgeo.contMDiffOn.continuousOn.mono hI)
  have hcross : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ frontier A := by
    by_contra h
    push Not at h
    have hdisj : Disjoint (γ '' Icc (0 : ℝ) 1) (frontier A) := by
      apply disjoint_left.mpr
      rintro y ⟨t, ht, rfl⟩ hy
      exact h t ht hy
    have hsub := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      hconn hdisj ⟨x, ⟨1, by simp, hγ1⟩, hA.interior_eq.symm ▸ hx⟩
    exact hp (interior_subset (hsub ⟨0, by simp, hγ0⟩))
  obtain ⟨t, ht, hty⟩ := hcross
  have hpyt : (g.edist p (γ t)).toReal = t * (g.edist p x).toReal := by
    have h := hmin 0 (by simp) t ht
    rw [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.1]
  have hxyt : (g.edist x (γ t)).toReal = (1 - t) * (g.edist p x).toReal := by
    have h := hmin 1 (by simp) t ht
    rw [hγ1, abs_of_nonneg (sub_nonneg.mpr ht.2)] at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)]
  refine ⟨γ t, hty, ?_⟩
  have htriangle := g.toReal_edist_triangle p (γ t) z
  have hbound := hdiam (γ t) hty z hz
  rw [hpyt] at htriangle
  rw [hxyt]
  nlinarith

end PoincareMT.RiemannianMetric.RadialHomeomorph
