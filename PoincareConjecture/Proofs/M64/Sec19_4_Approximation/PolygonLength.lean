import PoincareConjecture.Definitions.M64Approximation













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators intervalIntegral Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}

private theorem cellLength_pos {N : ℕ} (hN : 0 < N) : 0 < m63CellLength N := by
  dsimp only [m63CellLength]
  exact div_pos Real.two_pi_pos (by exact_mod_cast hN)

private theorem count_mul_cellLength {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * m63CellLength N = curvePeriod := by
  dsimp only [m63CellLength, curvePeriod]
  field_simp

omit [IsManifold (𝓡 n) ∞ M] in
private theorem curveVelocity_comp_local {gamma : ℝ → M} {phi : ℝ → ℝ} {x v : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x))
    (hphi : HasDerivAt phi v x) :
    curveVelocity (n := n) (fun y => gamma (phi y)) x =
      v • curveVelocity (n := n) gamma (phi x) := by
  have hvalue : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) phi x 1 = v := by
    rw [mfderiv_eq_fderiv, hphi.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ v
  have hcomp := mfderiv_comp_apply (f := phi) (g := gamma) x hgamma
    hphi.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (1 : ℝ)
  exact hcomp.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x)) hvalue).trans (by
    simpa only [curveVelocity, smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma (phi x)).map_smul v (1 : ℝ)))

private theorem polygon_cell_speed_ae
    (polygon : M63GeodesicPolygon g D N) (hN : 0 < N)
    (j : Fin N) :
    ∀ᵐ x : ℝ ∂volume,
      x ∈ Set.uIoc (m63CellLeft N j)
        (m63CellLeft N j + m63CellLength N) →
      g.tangentNorm (polygon.map x)
          (curveVelocity (n := n) polygon.map x) =
        (polygon.side j).speed := by
  let ell := m63CellLength N
  let left := m63CellLeft N j
  let right := left + ell
  have hell : 0 < ell := cellLength_pos hN
  have hleft : left < right := by dsimp [right]; linarith
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ right := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx hxu
  have hxu' : x ∈ Ioc left right := by
    simpa only [uIoc_of_le hleft.le, left, right, ell] using hxu
  have hxint : x ∈ Ioo left right := ⟨hxu'.1, lt_of_le_of_ne hxu'.2 hx⟩
  let S : Set ℝ := Icc left right
  have hxS : x ∈ S := ⟨hxint.1.le, hxint.2.le⟩
  have hmap : EqOn polygon.map ((polygon.side j).map ∘ (fun y => y - left)) S := by
    intro y hy
    have hys : y - left ∈ Icc 0 ell := by
      dsimp [S, left, right, ell] at hy ⊢
      constructor <;> linarith [hy.1, hy.2]
    simpa [left, Function.comp_apply, sub_add_cancel] using polygon.cell_agreement j (y - left) hys
  have hysx : x - left ∈ Icc 0 ell := by
    dsimp [left, right, ell] at hxint ⊢
    constructor <;> linarith [hxint.1, hxint.2]
  have hsideAt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n)
      (polygon.side j).map (x - left) :=
    ((polygon.side j).smooth.contMDiffAt
      ((polygon.side j).domain_open.mem_nhds
        ((polygon.side j).interval_subset hysx))).mdifferentiableAt (by simp)
  have hside : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n)
      ((polygon.side j).map ∘ (fun y : ℝ => y - left)) x :=
    hsideAt.comp x ((hasDerivAt_id x).sub_const left).differentiableAt.mdifferentiableAt
  have hflat : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) polygon.map x := by
    have hEqAt : polygon.map =ᶠ[𝓝 x] (polygon.side j).map ∘ (fun y : ℝ => y - left) :=
      by
        filter_upwards [isOpen_Ioo.mem_nhds hxint] with y hy
        exact hmap ⟨hy.1.le, hy.2.le⟩
    exact hside.congr_of_eventuallyEq hEqAt
  have hunique : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) S x :=
    ((uniqueDiffOn_Icc hleft) x hxS).uniqueMDiffWithinAt
  have hderiv := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ))
    (I' := 𝓡 n) hmap hxS
  rw [mfderivWithin_eq_mfderiv hunique hflat,
    mfderivWithin_eq_mfderiv hunique hside] at hderiv
  have hvelocity : curveVelocity (n := n) polygon.map x =
      curveVelocity (n := n) ((polygon.side j).map ∘ (fun y : ℝ => y - left)) x := by
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) polygon.map x 1 = _
    exact congrArg (fun L => L 1) hderiv
  have hpoint : polygon.map x = (polygon.side j).map (x - left) := hmap hxS
  rw [hpoint, hvelocity]
  have hphi : HasDerivAt (fun y : ℝ => y - left) 1 x :=
    (hasDerivAt_id x).sub_const left
  change g.tangentNorm ((polygon.side j).map (x - left))
    (curveVelocity (n := n) (fun y : ℝ => (polygon.side j).map (y - left)) x) = _
  rw [curveVelocity_comp_local (gamma := (polygon.side j).map)
    (phi := fun y : ℝ => y - left) (x := x) (v := 1) hsideAt hphi]
  simpa only [Function.comp_apply, curveVelocity, one_smul] using
    ((polygon.side j).constant_speed (x - left) (by
      dsimp [left, right, ell] at hxint ⊢
      constructor <;> linarith [hxint.1, hxint.2]))




theorem m64PolygonLength_eq_sum
    (polygon : M63GeodesicPolygon g D N) (hN : 0 < N) :
    m64PolygonLength polygon =
      ∑ j : Fin N, m63CellLength N * (polygon.side j).speed := by
  let ell := m63CellLength N
  have hell : 0 < ell := cellLength_pos hN
  have hcell (j : Fin N) :
      (∫ x in m63CellLeft N j..(m63CellLeft N j + ell),
        g.tangentNorm (polygon.map x) (curveVelocity (n := n) polygon.map x)) =
        ell * (polygon.side j).speed := by
    have hEq : (fun x => g.tangentNorm (polygon.map x)
        (curveVelocity (n := n) polygon.map x)) =ᵐ[volume.restrict
          (Set.uIoc (m63CellLeft N j) (m63CellLeft N j + ell))]
        (fun _ => (polygon.side j).speed) := by
      apply (ae_restrict_iff' measurableSet_uIoc).2
      simpa only [ell] using polygon_cell_speed_ae polygon hN j
    rw [intervalIntegral.integral_congr_ae_restrict hEq]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    dsimp [ell]
    ring
  have hsum :
      (∑ j : Fin N, ∫ x in m63CellLeft N j..(m63CellLeft N j + ell),
        g.tangentNorm (polygon.map x) (curveVelocity (n := n) polygon.map x)) =
      ∫ x in (0 : ℝ)..curvePeriod,
        g.tangentNorm (polygon.map x) (curveVelocity (n := n) polygon.map x) := by
    have htel := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * ell) (n := N) (μ := volume)
      (fun j hj => by
        let jj : Fin N := ⟨j, hj⟩
        have hEq : (fun x => g.tangentNorm (polygon.map x)
            (curveVelocity (n := n) polygon.map x)) =ᵐ[volume.restrict
              (Set.uIoc (m63CellLeft N jj)
                (m63CellLeft N jj + ell))]
            (fun _ => (polygon.side jj).speed) := by
          apply (ae_restrict_iff' measurableSet_uIoc).2
          simpa only [ell, jj] using polygon_cell_speed_ae polygon hN jj
        have hint := (intervalIntegrable_congr_ae hEq).mpr intervalIntegrable_const
        simpa only [m63CellLeft, ell, Nat.cast_add, Nat.cast_one, add_mul,
          one_mul] using hint)
    rw [← Fin.sum_univ_eq_sum_range] at htel
    simpa only [m63CellLeft, ell, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Nat.cast_zero, zero_mul, count_mul_cellLength hN, curvePeriod] using htel
  change (∫ x in (0 : ℝ)..curvePeriod,
      g.tangentNorm (polygon.map x) (curveVelocity (n := n) polygon.map x)) = _
  rw [← hsum]
  exact Finset.sum_congr rfl (fun j _ => hcell j)

end PoincareConjecture
