import PoincareConjecture.Statements.M60Area
import PoincareConjecture.Statements.M61Width

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

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

end PoincareConjecture
