import PoincareConjecture.Proofs.M14.Sec6_2_OpenSurfaceDensity










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {α : ℝ × ℝ → G.Point} {J P : Set ℝ} {T s v d : ℝ}




theorem surfaceEulerPair_eq_zero (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    (hclock : ∀ z ∈ J ×ˢ P, G.spacetime.timeFunction (α z) = T - z.1)
    (hs : s ∈ J) (hv : v ∈ P) (hspos : 0 < s)
    (E : M14PullbackExtension G (fun r => α (r, v)) J (fun r => surfaceHorizontalFst α r v))
    (hmomentum : HasDerivAt
      (fun r => 2 * Real.sqrt r * G.spacetime.horizontalMetric.inner (α (r, v))
        (surfaceHorizontalFst α r v) (surfaceHorizontalSnd α r v)) d s)
    (hdensity : HasDerivAt
      (fun u => M14RawLIntegrand G (fun r => α (r, u)) (fun r => surfaceHorizontalFst α r u) s)
      d v) :
    G.spacetime.horizontalMetric.inner (α (s, v))
        (M14HorizontalCovariantDerivative G (fun r => α (r, v)) J
          (fun r => surfaceHorizontalFst α r v) E s) (surfaceHorizontalSnd α s v) -
      (1 / 2 : ℝ) * M14HorizontalScalarDifferential G (α (s, v)) (surfaceHorizontalSnd α s v).val +
      (1 / (2 * s) : ℝ) * G.spacetime.horizontalMetric.inner (α (s, v))
        (surfaceHorizontalFst α s v) (surfaceHorizontalSnd α s v) +
      2 * horizontalRicci G.leafwise (α (s, v))
        (surfaceHorizontalFst α s v) (surfaceHorizontalSnd α s v) = 0 := by
  obtain ⟨F⟩ := exists_surfaceHorizontalSnd_extension hJ hP hα hv
  obtain ⟨EU⟩ := exists_surfaceHorizontalFst_parameter_extension hJ hP hα hs
  have hvar := hasDerivAt_surfaceRawDensity hM12 hJ hP hα hclock hs hv EU
  have htorsion := horizontalCovariantDerivative_surface_commute hCoordinates
    (hJ.prod hP) hα ⟨hs, hv⟩ (hJ.mem_nhds hs) (hP.mem_nhds hv) F EU
  rw [← htorsion] at hvar
  have hpair := hasDerivAt_surfaceWeightedPair hJ hP hα hclock hs hv hspos E F
  have heq := (hpair.unique hmomentum).trans (hdensity.unique hvar)
  have hsqrt : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hspos).ne'
  have hweight : (1 / Real.sqrt s : ℝ) = 2 * Real.sqrt s * (1 / (2 * s)) := by
    field_simp [hsqrt, hspos.ne']
    nlinarith [Real.sq_sqrt hspos.le]
  rw [hweight] at heq
  have hz : 2 * Real.sqrt s *
      (G.spacetime.horizontalMetric.inner (α (s, v))
          (M14HorizontalCovariantDerivative G (fun r => α (r, v)) J
            (fun r => surfaceHorizontalFst α r v) E s) (surfaceHorizontalSnd α s v) -
        (1 / 2 : ℝ) * M14HorizontalScalarDifferential G (α (s, v))
          (surfaceHorizontalSnd α s v).val +
        (1 / (2 * s) : ℝ) * G.spacetime.horizontalMetric.inner (α (s, v))
          (surfaceHorizontalFst α s v) (surfaceHorizontalSnd α s v) +
        2 * horizontalRicci G.leafwise (α (s, v))
          (surfaceHorizontalFst α s v) (surfaceHorizontalSnd α s v)) = 0 := by
    linear_combination heq
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero two_ne_zero hsqrt)

end PoincareConjecture.M14
