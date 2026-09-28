import PoincareConjecture.Proofs.M35.Thm12_28.NeckAxialMetric
import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureLimit

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

theorem exists_backward_cylinder_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ u ∈ Icc (-1 : ℝ) 0,
        ∀ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
          (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x)
          (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
          RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate) →
            D.curvatureTensorNorm (N.coordinate (q, s)) < 2 := by
  classical
  by_contra h
  push Not at h
  have hbad (n : ℕ) := h (min (1 / 4) (1 / ((n : ℝ) + 1))) (by positivity)
  choose epsilon he hemax u hu g D x N q s hs hclose hlarge using hbad
  have hk (n : ℕ) : 2 ≤ ⌊(epsilon n)⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ (he n)]
    norm_num
    linarith [(hemax n).trans (min_le_left (1 / 4) (1 / ((n : ℝ) + 1)))]
  have hezero : Tendsto epsilon atTop (𝓝 0) :=
    squeeze_zero (fun n => (he n).le)
      (fun n => (hemax n).trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨u', hu', phi, hphi, htime⟩ := isCompact_Icc.tendsto_subseq hu
  have huone : u' < 1 := hu'.2.trans_lt (by norm_num)
  have hreal (n : ℕ) :=
    (N n).exists_axial_curvature_realization (g n) (D n) (q n) (s n) (hs n)
  choose G DG hG hnorm using hreal
  have hlimit := cylinder_curvatureTensorNorm_tendsto_of_time_tendsto
    (fun n => G (phi n)) (fun n => DG (phi n)) (fun n => epsilon (phi n))
    (fun n => roundCylinderPullback (g (phi n)) (N (phi n)).coordinate)
    (fun n => q (phi n)) (fun n => s (phi n)) (fun n => u (phi n)) u' huone
    (fun n => hs (phi n)) (fun n => hu (phi n)) (fun n => he (phi n))
    (fun n => hk (phi n)) (fun n => hclose (phi n))
    (hezero.comp hphi.tendsto_atTop) htime (fun n => hG (phi n))
  have hmodel : 1 / (1 - u') < (2 : ℝ) := by
    have hpos : 0 < 1 - u' := sub_pos.mpr huone
    apply (div_lt_iff₀ hpos).mpr
    linarith [hu'.2]
  obtain ⟨n, hn⟩ := (hlimit.eventually (gt_mem_nhds hmodel)).exists
  have hge := hlarge (phi n)
  rw [← hnorm (phi n)] at hge
  linarith

theorem exists_backward_neck_carrier_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ u ∈ Icc (-1 : ℝ) 0,
        ∀ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
          (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x),
          RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate) →
            ∀ y ∈ N.carrier, D.curvatureTensorNorm y < 2 := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_backward_cylinder_curvature_bound
  refine ⟨delta, hdelta, fun epsilon he hedelta u hu g D x N hclose y hy => ?_⟩
  rw [← N.coordinate_image] at hy
  obtain ⟨⟨q, s⟩, hs, rfl⟩ := hy
  exact hbound epsilon he hedelta u hu g D x N q s hs.2 hclose

end PoincareConjecture.M35
