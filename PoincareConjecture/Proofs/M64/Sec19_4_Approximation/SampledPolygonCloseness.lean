import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SampledPolygonLength
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellBoundaryNull













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




theorem m64_c1_subarc_edist_le_speed
    (g : RiemannianMetric n M) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    {S s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ curvePeriod)
    (hbound : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (gamma x) (curveVelocity gamma x) ≤ S) :
    g.edist (gamma s) (gamma t) ≤ ENNReal.ofReal (S * (t - s)) := by
  have hd := g.edist_le_pathELength_of_mem_Icc hgamma.contMDiffOn
    (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
  rw [M04.pathELength_eq_ofReal_integral_pathSpeed g hgamma hst] at hd
  apply hd.trans (ENNReal.ofReal_le_ofReal ?_)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hst
    ((M04.continuous_pathSpeed g hgamma).intervalIntegrable s t)
    (continuous_const.intervalIntegrable s t)
    (fun x hx => hbound x ⟨hs.trans hx.1, hx.2.trans ht⟩)
  simpa only [M04.pathSpeed, curveVelocity, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm] using hi




theorem m64_minimizing_side_prefix_edist_le
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {ell s : ℝ} {p q : M}
    (side : M63MinimizingGeodesicSide g D ell p q)
    (hs : s ∈ Icc (0 : ℝ) ell) :
    g.edist p (side.map s) ≤ g.edist p q := by
  have hside : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 side.map (Icc (0 : ℝ) ell) :=
    (side.smooth.of_le (m := 1) (by norm_num)).mono side.interval_subset
  have hd := g.edist_le_pathELength_of_mem_Icc hside hs
  simpa only [side.start, side.minimizing] using hd





theorem m64_sampled_polygon_cell_edist_le
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N) (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiodic : Function.Periodic gamma curvePeriod)
    (hvertices : ∀ j : Fin N, polygon.vertices j = gamma (m63CellLeft N j))
    {S : ℝ} (hS : 0 ≤ S)
    (hbound : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (gamma x) (curveVelocity gamma x) ≤ S)
    (j : Fin N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (m63CellLength N)) :
    g.edist (gamma (m63CellLeft N j + s))
      (polygon.map (m63CellLeft N j + s)) ≤
        ENNReal.ofReal (2 * S * m63CellLength N) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hell : 0 < m63CellLength N := m63CellLength_pos hN
  have hleft : 0 ≤ m63CellLeft N j :=
    mul_nonneg (Nat.cast_nonneg _) hell.le
  have hj : (j.val : ℝ) + 1 ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hright : m63CellLeft N j + m63CellLength N ≤ curvePeriod := by
    calc
      _ = ((j.val : ℝ) + 1) * m63CellLength N := by
        dsimp only [m63CellLeft]
        ring
      _ ≤ (N : ℝ) * m63CellLength N :=
        mul_le_mul_of_nonneg_right hj hell.le
      _ = curvePeriod := m63_count_mul_cellLength hN
  have hadj : g.edist (polygon.vertices j) (polygon.vertices (finRotate N j)) ≤
      ENNReal.ofReal (S * m63CellLength N) := by
    rw [hvertices j, hvertices (finRotate N j),
      m63PeriodicLoop_cell_finish hperiodic hN j]
    simpa only [add_sub_cancel_left] using
      m64_c1_subarc_edist_le_speed g hgamma hleft
        (le_add_of_nonneg_right hell.le) hright hbound
  have hside : g.edist (polygon.vertices j) ((polygon.side j).map s) ≤
      ENNReal.ofReal (S * m63CellLength N) :=
    (m64_minimizing_side_prefix_edist_le (polygon.side j) hs).trans hadj
  have horiginal : g.edist (polygon.vertices j)
      (gamma (m63CellLeft N j + s)) ≤
        ENNReal.ofReal (S * m63CellLength N) := by
    rw [hvertices j]
    have h := m64_c1_subarc_edist_le_speed g hgamma hleft
      (le_add_of_nonneg_right hs.1)
      (by linarith [hs.2]) hbound
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left hs.2 hS
  rw [polygon.cell_agreement j s hs]
  have htri : g.edist (gamma (m63CellLeft N j + s)) ((polygon.side j).map s) ≤
      g.edist (gamma (m63CellLeft N j + s)) (polygon.vertices j) +
        g.edist (polygon.vertices j) ((polygon.side j).map s) :=
    Manifold.riemannianEDist_triangle
  have hrev : g.edist (gamma (m63CellLeft N j + s)) (polygon.vertices j) =
      g.edist (polygon.vertices j) (gamma (m63CellLeft N j + s)) :=
    Manifold.riemannianEDist_comm
  rw [hrev] at htri
  apply (htri.trans (add_le_add horiginal hside)).trans_eq
  rw [← ENNReal.ofReal_add (mul_nonneg hS hell.le) (mul_nonneg hS hell.le)]
  congr 1
  ring




theorem m64_sampled_polygon_edist_le
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N) (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiodic : Function.Periodic gamma curvePeriod)
    (hvertices : ∀ j : Fin N, polygon.vertices j = gamma (m63CellLeft N j))
    {S : ℝ} (hS : 0 ≤ S)
    (hbound : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (gamma x) (curveVelocity gamma x) ≤ S) :
    ∀ x : ℝ, g.edist (gamma x) (polygon.map x) ≤
      ENNReal.ofReal (2 * S * m63CellLength N) := by
  have hon {x : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      g.edist (gamma x) (polygon.map x) ≤
        ENNReal.ofReal (2 * S * m63CellLength N) := by
    obtain ⟨j, hj⟩ := m64_polygon_cells_cover hN (annulusPoint x 0)
      (show annulusPoint x 0 ∈ m64AnnulusDomain from
        ⟨hx.1, hx.2, le_rfl, zero_le_one⟩)
    change m63CellLeft N j ≤ x ∧
      x ≤ m63CellLeft N j + m63CellLength N ∧
        0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 at hj
    have hs : x - m63CellLeft N j ∈ Icc (0 : ℝ) (m63CellLength N) := by
      constructor <;> linarith [hj.1, hj.2.1]
    have hh := m64_sampled_polygon_cell_edist_le hN polygon hgamma hperiodic
      hvertices hS hbound j hs
    rw [show m63CellLeft N j + (x - m63CellLeft N j) = x by ring] at hh
    exact hh
  intro x
  let k : ℤ := Int.floor (x / curvePeriod)
  let y : ℝ := x - (k : ℝ) * curvePeriod
  have hy : y ∈ Icc (0 : ℝ) curvePeriod := by
    have h0 := (le_div_iff₀ Real.two_pi_pos).mp (Int.floor_le (x / curvePeriod))
    have h1 := (div_lt_iff₀ Real.two_pi_pos).mp
      (Int.lt_floor_add_one (x / curvePeriod))
    dsimp only [y, k]
    dsimp only [curvePeriod] at h0 h1 ⊢
    constructor <;> linarith only [h0, h1]
  have hx : x = y + (k : ℝ) * curvePeriod := by dsimp only [y]; ring
  rw [hx, hperiodic.int_mul k y, polygon.periodic.int_mul k y]
  exact hon hy

end PoincareConjecture
