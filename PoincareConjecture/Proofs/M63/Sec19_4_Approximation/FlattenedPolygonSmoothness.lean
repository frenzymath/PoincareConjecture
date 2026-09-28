import PoincareConjecture.Proofs.M63.Mathlib.FlatCellComposition
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlatteningCells










set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}



theorem M63GeodesicPolygon.integer_cell (polygon : M63GeodesicPolygon g D N)
    (hN : 0 < N) (j : ℤ) :
    ∃ i : Fin N, ∀ s ∈ Set.Icc 0 (m63CellLength N),
      polygon.map ((j : ℝ) * m63CellLength N + s) = (polygon.side i).map s := by
  let i : Fin N := ⟨j.natMod N, Int.natMod_lt hN.ne'⟩
  have hirem : (i.val : ℤ) = j % (N : ℤ) :=
    Int.natCast_toNat_eq_self.mpr (Int.emod_nonneg j (by exact_mod_cast hN.ne'))
  have hdecomp : (j : ℝ) = (i.val : ℝ) + ((j / (N : ℤ) : ℤ) : ℝ) * (N : ℝ) := by
    have hz : j = (i.val : ℤ) + j / (N : ℤ) * (N : ℤ) := by
      rw [hirem]
      exact (Int.emod_add_ediv_mul j N).symm
    exact_mod_cast hz
  refine ⟨i, fun s hs => ?_⟩
  have hperiod : (N : ℝ) * m63CellLength N = curvePeriod := m63_count_mul_cellLength hN
  have hshift : (j : ℝ) * m63CellLength N + s =
      (i.val : ℝ) * m63CellLength N + s + ((j / (N : ℤ) : ℤ) : ℝ) * curvePeriod := by
    rw [hdecomp, ← hperiod]
    ring
  rw [hshift, polygon.periodic.int_mul (j / (N : ℤ))]
  exact polygon.cell_agreement i s hs



theorem m63FlattenedPolygon_periodic (polygon : M63GeodesicPolygon g D N) (hN : 0 < N) :
    Function.Periodic (m63FlattenedPolygon polygon) curvePeriod := by
  intro x
  change polygon.map (m63Flattening N (x + curvePeriod)) = polygon.map (m63Flattening N x)
  rw [m63Flattening_period_shift hN, polygon.periodic]



theorem m63FlattenedPolygon_smooth (polygon : M63GeodesicPolygon g D N) (hN : 0 < N) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (m63FlattenedPolygon polygon) := by
  classical
  have hcells : ∀ j : ℤ, ∃ alpha : ℝ → M,
      (∀ s ∈ Set.Icc 0 (m63CellLength N), ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ alpha s) ∧
      ∀ s ∈ Set.Icc 0 (m63CellLength N),
        polygon.map ((j : ℝ) * m63CellLength N + s) = alpha s := by
    intro j
    obtain ⟨i, hi⟩ := polygon.integer_cell hN j
    refine ⟨(polygon.side i).map, ?_, hi⟩
    intro s hs
    exact (polygon.side i).smooth.contMDiffAt
      ((polygon.side i).domain_open.mem_nhds ((polygon.side i).interval_subset hs))
  choose alpha halpha hagreement using hcells
  change ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (polygon.map ∘ m63Flattening N)
  exact contMDiff_comp_of_flat_cells (𝓡 n) (m63CellLength_pos hN) alpha halpha hagreement
    (m63Flattening_smooth N) (m63Flattening_strictMono hN) (m63Flattening_vertex hN)
    (fun j _ hi => m63Flattening_flat hN hi j)

end PoincareConjecture
