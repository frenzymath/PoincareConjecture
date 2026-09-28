import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlattenedPolygonSmoothness
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.MinimizingGeodesicSide

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}

theorem m63FlattenedPolygon_cell_agreement (polygon : M63GeodesicPolygon g D N)
    (hN : 0 < N) (j : Fin N) {s : ℝ} (hs : s ∈ Icc 0 (m63CellLength N)) :
    m63FlattenedPolygon polygon (m63CellLeft N j + s) =
      (polygon.side j).map (m63Flattening N (m63CellLeft N j + s) - m63CellLeft N j) := by
  have hy : m63Flattening N (m63CellLeft N j + s) - m63CellLeft N j ∈
      Icc 0 (m63CellLength N) := by
    simpa only [Int.cast_natCast, m63CellLeft] using m63Flattening_mem_cell hN (j.val : ℤ) hs
  have ha := polygon.cell_agreement j _ hy
  change polygon.map (m63Flattening N (m63CellLeft N j + s)) = _
  simpa only [← add_sub_assoc, add_sub_cancel_left] using ha

theorem m63FlattenedPolygon_cell_velocity (polygon : M63GeodesicPolygon g D N)
    (hN : 0 < N) (j : Fin N) {s : ℝ} (hs : s ∈ Icc 0 (m63CellLength N)) :
    let x := m63CellLeft N j + s
    let y := m63Flattening N x - m63CellLeft N j
    m63AngularFirstJet (m63FlattenedPolygon polygon) x =
      (⟨(polygon.side j).map y,
        m63Profile N x • curveVelocity (n := n) (polygon.side j).map y⟩ :
          TangentBundle (𝓡 n) M) := by
  let x := m63CellLeft N j + s
  let psi : ℝ → ℝ := fun z => m63Flattening N z - m63CellLeft N j
  have hy : psi x ∈ Icc 0 (m63CellLength N) := by
    simpa only [psi, x, m63CellLeft, Int.cast_natCast] using
      m63Flattening_mem_cell hN (j.val : ℤ) hs
  have hside : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (polygon.side j).map (psi x) :=
    ((polygon.side j).smooth.contMDiffAt
      ((polygon.side j).domain_open.mem_nhds
        ((polygon.side j).interval_subset hy))).mdifferentiableAt (by simp)
  have hpsi : HasDerivAt psi (m63Profile N x) x :=
    (m63Flattening_hasDerivAt N x).sub_const _
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) ((polygon.side j).map ∘ psi) x :=
    hside.comp x hpsi.differentiableAt.mdifferentiableAt
  have hflat : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (m63FlattenedPolygon polygon) x :=
    (m63FlattenedPolygon_smooth polygon hN).mdifferentiableAt (by simp)
  let S := Icc (m63CellLeft N j) (m63CellLeft N j + m63CellLength N)
  have hx : x ∈ S := by
    change m63CellLeft N j ≤ m63CellLeft N j + s ∧
      m63CellLeft N j + s ≤ m63CellLeft N j + m63CellLength N
    constructor <;> linarith [hs.1, hs.2]
  have hEq : EqOn (m63FlattenedPolygon polygon) ((polygon.side j).map ∘ psi) S := by
    intro z hz
    have hzs : z - m63CellLeft N j ∈ Icc 0 (m63CellLength N) := by
      have hz' : m63CellLeft N j ≤ z ∧ z ≤ m63CellLeft N j + m63CellLength N := hz
      constructor <;> linarith [hz'.1, hz'.2]
    have ha := m63FlattenedPolygon_cell_agreement polygon hN j hzs
    simpa only [← add_sub_assoc, add_sub_cancel_left, Function.comp_apply, psi] using ha
  have hunique : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) S x :=
    ((uniqueDiffOn_Icc (show m63CellLeft N j < m63CellLeft N j + m63CellLength N by
      linarith [m63CellLength_pos hN])) x hx).uniqueMDiffWithinAt
  have hderiv := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) hEq hx
  rw [mfderivWithin_eq_mfderiv hunique hflat, mfderivWithin_eq_mfderiv hunique hcomp] at hderiv
  have hvelocity : curveVelocity (n := n) (m63FlattenedPolygon polygon) x =
      m63Profile N x • curveVelocity (n := n) (polygon.side j).map (psi x) := by
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (m63FlattenedPolygon polygon) x 1 = _
    rw [hderiv]
    exact M63.curveVelocity_comp hside hpsi
  apply TotalSpace.ext (m63FlattenedPolygon_cell_agreement polygon hN j hs)
  exact heq_of_eq hvelocity

theorem m63FlattenedPolygon_cell_speed (polygon : M63GeodesicPolygon g D N)
    (hN : 0 < N) (j : Fin N) {s : ℝ} (hs : s ∈ Icc 0 (m63CellLength N)) :
    let x := m63CellLeft N j + s
    g.tangentNorm (m63FlattenedPolygon polygon x)
      (curveVelocity (n := n) (m63FlattenedPolygon polygon) x) =
      (polygon.side j).speed * m63Profile N x := by
  let x := m63CellLeft N j + s
  let y := m63Flattening N x - m63CellLeft N j
  have hj := m63FlattenedPolygon_cell_velocity polygon hN j hs
  have hpoint := congrArg (fun z : TangentBundle (𝓡 n) M => z.proj) hj
  have hvelocity := congrArg (fun z : TangentBundle (𝓡 n) M => z.2) hj
  change g.tangentNorm (m63FlattenedPolygon polygon x)
    (curveVelocity (n := n) (m63FlattenedPolygon polygon) x) = _
  change curveVelocity (n := n) (m63FlattenedPolygon polygon) x =
    m63Profile N x • curveVelocity (n := n) (polygon.side j).map y at hvelocity
  change m63FlattenedPolygon polygon x = (polygon.side j).map y at hpoint
  have hy : y ∈ Icc 0 (m63CellLength N) := by
    simpa only [y, x, m63CellLeft, Int.cast_natCast] using
      m63Flattening_mem_cell hN (j.val : ℤ) hs
  rw [hvelocity, hpoint, g.tangentNorm_smul, abs_of_nonneg (m63Profile_nonneg hN x),
    (polygon.side j).constant_speed y hy, mul_comm]

end PoincareConjecture
