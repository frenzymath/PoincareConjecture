import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Theory
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Theory

/-!
# M61 checked sphere and short-family consequences

Morgan--Tian Lemma 18.10, pp. 424-426, supplies the sphere minimum through
M60. Definition 18.17, p. 430, and corrected Corollary 18.28, p. 434, give
the short-family bound at its actual maximizing parameter. These adapters
retain the same metric, area functional and M60 short-loop threshold.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- M60's positive threshold and branched minimizer identify the actual
infimum over all C1 non-null sphere maps. -/
theorem m61SphereWidth_from_M60
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (P60 : M60LeastSphereAreaConclusion g) :
    M61SphereWidthProperties g := by
  obtain ⟨e₀, he₀, hsmall, f, hminimal, hnonnull, harea⟩ := P60
  have hleast : IsLeast (m61SphereAreaRange g) e₀ := by
    refine ⟨?_, ?_⟩
    · exact ⟨f, hminimal.smooth.of_le (by simp), hnonnull, harea⟩
    · rintro a ⟨h, hregular, hnontrivial, rfl⟩
      exact le_of_not_gt (fun hlt => hnontrivial (hsmall h hregular hlt))
  have hwidth : m61SphereWidth g = e₀ := hleast.csInf_eq
  refine ⟨?_, ?_, f, hminimal, hnonnull, harea.trans hwidth.symm⟩
  · simpa only [hwidth] using he₀
  · simpa only [hwidth] using hleast

/-- Apply M60's unchanged short-loop threshold to the maximizing member of
the displayed raw null family. -/
theorem m61ShortFamilyWidth_from_M60
    (core : M61RawWidthCore.{u}) (shortLoop : M60ShortLoopAreaClaim.{u}) :
    M61ShortFamilyWidthClaim.{u} := by
  intro M _ _ _ _ _ g hcompact eta heta
  obtain ⟨zeta, hzeta, hzetabound, hsmall⟩ := shortLoop g hcompact eta heta
  refine ⟨zeta, hzeta, hzetabound, ?_⟩
  intro F hnull hlength
  obtain ⟨c, hc⟩ := (core.family g hcompact F hnull).attained
  obtain ⟨_, _, _, harea⟩ := hsmall (F c) (hlength c)
  rw [← hc]
  exact harea

end PoincareMT
