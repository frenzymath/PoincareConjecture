import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

theorem relative_inner_bounds_of_chart (g : RiemannianMetric n M)
    (h : RiemannianMetric n N) {e : M → N} {q x : M} {a b : ℝ}
    (hx : x ∈ (extChartAt (𝓡 n) q).source)
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e x)
    (hcoeff : ∀ u : EuclideanSpace ℝ (Fin n),
      a * g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
        ((extChartAt (𝓡 n) q) x) u u ≤
        h.pullbackCoefficients (e ∘ (extChartAt (𝓡 n) q).symm)
          ((extChartAt (𝓡 n) q) x) u u ∧
      h.pullbackCoefficients (e ∘ (extChartAt (𝓡 n) q).symm)
        ((extChartAt (𝓡 n) q) x) u u ≤
        b * g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
          ((extChartAt (𝓡 n) q) x) u u) (v : TangentSpace (𝓡 n) x) :
    a * g.inner x v v ≤ h.inner (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x v) ∧
    h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
      (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ b * g.inner x v v := by
  let c := extChartAt (𝓡 n) q
  have hcx : c.symm (c x) = x := c.left_inv hx
  have htarget : c x ∈ c.target := c.map_source hx
  have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm (c x)).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm htarget
  obtain ⟨A, hA⟩ := hi
  let u := A.symm v
  have hAv : mfderiv (𝓡 n) (𝓡 n) c.symm (c x) u = v := by
    rw [← hA]
    exact A.apply_symm_apply v
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c x) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds htarget)).mdifferentiableAt (by simp)
  have he' : MDifferentiableAt (𝓡 n) (𝓡 n) e (c.symm (c x)) := hcx.symm ▸ he
  have hbase : g.pullbackCoefficients c.symm (c x) u u = g.inner x v v := by
    change g.inner (c.symm (c x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) u)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) u) = _
    rw [hAv, hcx]
  have hsource : h.pullbackCoefficients (e ∘ c.symm) (c x) u u =
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x v) := by
    change h.inner (e (c.symm (c x)))
      (mfderiv (𝓡 n) (𝓡 n) (e ∘ c.symm) (c x) u)
      (mfderiv (𝓡 n) (𝓡 n) (e ∘ c.symm) (c x) u) = _
    rw [mfderiv_comp (c x) he' hc]
    change h.inner (e (c.symm (c x)))
      (mfderiv (𝓡 n) (𝓡 n) e (c.symm (c x))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) u))
      (mfderiv (𝓡 n) (𝓡 n) e (c.symm (c x))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) u)) = _
    rw [hAv, hcx]
  dsimp only [c] at hbase hsource
  simpa only [hbase, hsource] using hcoeff u

end PoincareConjecture.RiemannianMetric
