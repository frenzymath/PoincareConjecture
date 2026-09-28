import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.MinimizingGeodesicSide
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProfileBase
import PoincareConjecture.Proofs.M04.ShiEnergyPaths
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff intervalIntegral BigOperators

namespace PoincareConjecture



theorem m63PeriodicLoop_cell_finish {X : Type*} {gamma : ℝ → X}
    (hperiodic : Function.Periodic gamma curvePeriod) {N : ℕ} (hN : 0 < N) (j : Fin N) :
    gamma (m63CellLeft N (finRotate N j)) =
      gamma (m63CellLeft N j + m63CellLength N) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  by_cases hj : j = Fin.last k
  · subst j
    rw [finRotate_last]
    have hend : m63CellLeft (k + 1) (Fin.last k) + m63CellLength (k + 1) =
        curvePeriod := by
      simpa only [m63CellLeft, Fin.val_last, Nat.cast_succ, add_mul, one_mul, curvePeriod]
        using m63_count_mul_cellLength (Nat.succ_pos k)
    rw [hend]
    simpa [m63CellLeft] using (hperiodic 0).symm
  · congr 1
    simp only [m63CellLeft, coe_finRotate_of_ne_last hj, Nat.cast_add, Nat.cast_one]
    ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem M63MinimizingGeodesicSide.edist_eq_length {g : RiemannianMetric n M}
    {D : LeviCivitaData g} {ell : ℝ} {p q : M}
    (side : M63MinimizingGeodesicSide g D ell p q) (hell : 0 ≤ ell) :
    g.edist p q = ENNReal.ofReal (ell * side.speed) := by
  have hlength := g.pathELength_eq_of_tangentNorm_eq side.constant_speed
  rw [sub_zero] at hlength
  calc
    _ = g.pathELength side.map 0 ell := side.minimizing.symm
    _ = ENNReal.ofReal (side.speed * ell) :=
      hlength.trans (ENNReal.ofReal_mul' hell).symm
    _ = _ := congrArg ENNReal.ofReal (mul_comm _ _)




theorem m63SampledPolygonLengthComparison {a b : ℝ} (F : RicciFlow n M (Icc a b)) :
    M63SampledPolygonLengthComparison F := by
  intro t _ N hN polygon gamma hperiodic hsmooth hvertices
  let ell := m63CellLength N
  let g := F.metric t
  let v := M04.pathSpeed g gamma
  have hell : 0 < ell := m63CellLength_pos hN
  have hv : Continuous v := M04.continuous_pathSpeed g hsmooth
  have hcell (j : Fin N) : ell * (polygon.side j).speed ≤
      ∫ x in m63CellLeft N j..(m63CellLeft N j + ell), v x := by
    have hab : m63CellLeft N j ≤ m63CellLeft N j + ell := le_add_of_nonneg_right hell.le
    have hnonneg : 0 ≤ ∫ x in m63CellLeft N j..(m63CellLeft N j + ell), v x :=
      intervalIntegral.integral_nonneg hab (fun x _ => M04.pathSpeed_nonneg g gamma x)
    apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
    have hdist := g.edist_le_pathELength_of_mem_Icc hsmooth.contMDiffOn
      (show m63CellLeft N j + ell ∈ Icc (m63CellLeft N j) (m63CellLeft N j + ell)
        from ⟨hab, le_rfl⟩)
    have hside := (polygon.side j).edist_eq_length hell.le
    conv at hside =>
      lhs
      rw [hvertices j, hvertices (finRotate N j),
        m63PeriodicLoop_cell_finish hperiodic hN j]
    rw [M04.pathELength_eq_ofReal_integral_pathSpeed g hsmooth hab] at hdist
    exact hside.symm.le.trans hdist
  have hsum : (∑ j : Fin N, ∫ x in m63CellLeft N j..(m63CellLeft N j + ell), v x) =
      ∫ x in (0 : ℝ)..curvePeriod, v x := by
    have htel := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * ell) (n := N) (μ := MeasureTheory.volume)
      (fun _ _ => hv.intervalIntegrable _ _)
    rw [← Fin.sum_univ_eq_sum_range] at htel
    simpa only [ell, m63CellLeft, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Nat.cast_zero, zero_mul, m63_count_mul_cellLength hN, curvePeriod] using htel
  change (∑ j : Fin N, ell * (polygon.side j).speed) ≤ ∫ x in (0 : ℝ)..curvePeriod, v x
  exact (Finset.sum_le_sum (fun j _ => hcell j)).trans_eq hsum

end PoincareConjecture
