import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PeriodicBoundary
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicPolygon
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SampledPolygonLength
import PoincareConjecture.Proofs.M04.ShiEnergyPaths
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

theorem m64_sampled_polygon_exists
    (hcompact : IsCompact (univ : Set M))
    (gamma : C1FreeLoopSpace (M := M)) (N : ℕ) (hN : 0 < N) :
    ∃ polygon : M63GeodesicPolygon g D N,
      M64SampledPolygon gamma polygon ∧ Nonempty (M64PolygonBoundary polygon) := by
  let vertices : Polygon M N :=
    ⟨fun j => periodicFreeLoop gamma (m63CellLeft N j)⟩
  let gamma0 : ℝ → M := periodicFreeLoop gamma
  have hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma0 := by
    exact Proofs.M58.contMDiff_periodicFreeLoop gamma
  let speed : ℝ → ℝ := M04.pathSpeed g gamma0
  let radius : Fin N → ℝ := fun j =>
    (∫ x in m63CellLeft N j..(m63CellLeft N j + m63CellLength N), speed x) + 1
  have hradius : ∀ j, 0 < radius j := by
    intro j
    dsimp [radius]
    have hnonneg : 0 ≤ ∫ x in m63CellLeft N j..(m63CellLeft N j + m63CellLength N),
        speed x := by
      apply intervalIntegral.integral_nonneg
      · linarith [m63CellLength_pos hN]
      · intro x _
        exact M04.pathSpeed_nonneg g gamma0 x
    linarith
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  have hcompact_ball : ∀ j, IsCompact (closure (g.ball (vertices j) (radius j))) := by
    intro j
    exact hcompact.of_isClosed_subset isClosed_closure (by
      intro x _
      exact mem_univ x)
  have hnext : ∀ j, vertices (finRotate N j) ∈ g.ball (vertices j) (radius j) := by
    intro j
    have hdist := g.edist_le_pathELength_of_mem_Icc hgamma0.contMDiffOn
      (show m63CellLeft N j + m63CellLength N ∈
          Icc (m63CellLeft N j) (m63CellLeft N j + m63CellLength N) by
        exact ⟨le_add_of_nonneg_right (m63CellLength_pos hN).le, le_rfl⟩)
    rw [M04.pathELength_eq_ofReal_integral_pathSpeed g hgamma0 (by
      linarith [m63CellLength_pos hN])] at hdist
    have hlt : (∫ x in m63CellLeft N j..(m63CellLeft N j + m63CellLength N),
        speed x) < (∫ x in m63CellLeft N j..(m63CellLeft N j + m63CellLength N),
        speed x) + 1 := by linarith
    have hnonneg : 0 ≤ ∫ x in m63CellLeft N j..(m63CellLeft N j + m63CellLength N),
        speed x := by
      apply intervalIntegral.integral_nonneg
      · linarith [m63CellLength_pos hN]
      · intro x _
        exact M04.pathSpeed_nonneg g gamma0 x
    have hball := hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
      linarith)).mpr hlt)
    change g.edist (gamma0 (m63CellLeft N j))
      (gamma0 (m63CellLeft N (finRotate N j))) < ENNReal.ofReal (radius j)
    have hfinish : gamma0 (m63CellLeft N (finRotate N j)) =
        gamma0 (m63CellLeft N j + m63CellLength N) := by
      dsimp [gamma0]
      exact m63PeriodicLoop_cell_finish
        (Proofs.M58.periodic_periodicFreeLoop gamma) hN j
    rw [hfinish]
    simpa only [radius, speed, gamma0] using hball
  obtain ⟨polygon, hvertices⟩ :=
    M63.geodesicPolygon_nonempty_of_precompact_balls g D hN vertices radius
      hradius hcompact_ball hnext
  refine ⟨polygon, ?_, exists_polygon_boundary polygon⟩
  intro j
  simpa [vertices] using congrArg (fun p : Polygon M N => p.vertices j) hvertices

theorem m64_sampled_polygon_exists_with_length
    (hcompact : IsCompact (univ : Set M))
    (gamma : C1FreeLoopSpace (M := M)) (N : ℕ) (hN : 0 < N) :
    ∃ polygon : M63GeodesicPolygon g D N,
      M64SampledPolygon gamma polygon ∧
      Nonempty (M64PolygonBoundary polygon) ∧
      m64PolygonLength polygon =
        ∑ j : Fin N, m63CellLength N * (polygon.side j).speed := by
  obtain ⟨polygon, hsampled, hboundary⟩ :=
    m64_sampled_polygon_exists hcompact gamma N hN
  exact ⟨polygon, hsampled, hboundary, m64PolygonLength_eq_sum polygon hN⟩

theorem m64_static_polygon_fields
    (hcompact : IsCompact (univ : Set M)) :
    (∀ gamma : C1FreeLoopSpace (M := M), ∀ N : ℕ, 0 < N →
      ∃ polygon : M63GeodesicPolygon g D N,
        M64SampledPolygon gamma polygon ∧ Nonempty (M64PolygonBoundary polygon)) ∧
    (∀ N : ℕ, 0 < N → ∀ polygon : M63GeodesicPolygon g D N,
      m64PolygonLength polygon =
        ∑ j : Fin N, m63CellLength N * (polygon.side j).speed) := by
  constructor
  · intro gamma N hN
    exact m64_sampled_polygon_exists hcompact gamma N hN
  · intro N hN polygon
    exact m64PolygonLength_eq_sum polygon hN

end PoincareConjecture
