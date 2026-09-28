import PoincareConjecture.Proofs.M35.CapGeometry.InitialCylinderScalarLimit










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => StandardCapSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem initial_neck_scalar_realization
    (g : RiemannianMetric 3 V) (D : LeviCivitaData g)
    {length : ℝ} (hlength : 0 < length) {x : V}
    (N : StandardCylinderPatch length x) (q : UnitTwoSphere) :
    ∃ (G : RiemannianMetric 3 V) (DG : LeviCivitaData G),
      (∀ i j : Fin 3,
        (fun p : V => G.inner p (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
          (fun p => roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate)
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) (cylinderCoordinateEquiv p) i j)) ∧
      DG.scalarCurvature 0 = D.scalarCurvature (N.coordinate (q, 0)) := by
  have hp : (cylinderCoordinateEquiv (0 : V)).2 ∈ Ioo (-length) length := by
    simp only [map_zero, Prod.snd_zero, mem_Ioo]
    exact ⟨neg_neg_of_pos hlength, hlength⟩
  obtain ⟨G, DG, hG⟩ := N.exists_euclidean_metric_realization g q hp
  let U : Set V := {p | (cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp cylinderCoordinateEquiv.continuous)
  have hi : ∀ᶠ p in 𝓝 (0 : V),
      (mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ cylinderChart q) p).IsInvertible :=
    Filter.mem_of_superset (hU.mem_nhds hp) fun p hp =>
      N.euclideanChart_mfderiv_invertible q hp
  have hm : ∀ᶠ p in 𝓝 (0 : V), ∀ v w : V, G.inner p v w =
      g.inner (N.coordinate (cylinderChart q p))
        (mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ cylinderChart q) p v)
        (mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ cylinderChart q) p w) := by
    filter_upwards [hG] with p hp v w
    exact congrArg (fun B : V →L[ℝ] V →L[ℝ] ℝ => B v w) hp
  have hscalar := scalarCurvature_eq_pullback_euclidean DG D
    (N.euclideanChart_contMDiffAt q hp) hi hm
  have hcenter : cylinderChart q 0 = (q, 0) := by
    change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm (cylinderCoordinateEquiv 0).1,
      (cylinderCoordinateEquiv 0).2) = _
    rw [map_zero]
    apply Prod.ext
    · have h := (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
        (mem_chart_source (EuclideanSpace ℝ (Fin 2)) q)
      simpa only [sphere_chart_center, Prod.fst_zero] using h
    · rfl
  refine ⟨G, DG, fun i j => N.euclidean_realization_coefficient_germ g q hp G hG i j, ?_⟩
  exact hscalar.trans (congrArg D.scalarCurvature (congrArg N.coordinate hcenter))



theorem exists_initial_cylinder_scalar_control {theta eta : ℝ}
    (htheta : theta < 1) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ u ∈ Icc (0 : ℝ) theta,
        ∀ (g : RiemannianMetric 3 V) (D : LeviCivitaData g)
          (x : V) (N : StandardCylinderPatch epsilon⁻¹ x) (q : UnitTwoSphere),
          RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate) →
            |(1 - u) * D.scalarCurvature (N.coordinate (q, 0)) - 1| < eta := by
  classical
  by_contra h
  push Not at h
  have hbad (n : ℕ) := h (min (1 / 4) (1 / ((n : ℝ) + 1))) (by positivity)
  choose epsilon he hemax u hu g D x N q hclose hlarge using hbad
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
  have huone : u' < 1 := hu'.2.trans_lt htheta
  choose G DG hG hscalar using fun n =>
    initial_neck_scalar_realization (g n) (D n) (inv_pos.mpr (he n)) (N n) (q n)
  have hlimit := cylinder_scalarCurvature_tendsto_of_time_tendsto
    (fun n => G (phi n)) (fun n => DG (phi n)) (fun n => epsilon (phi n))
    (fun n => roundCylinderPullback (g (phi n)) (N (phi n)).coordinate)
    (fun n => q (phi n)) (fun _ => 0) (fun n => u (phi n)) u' huone
    (fun n => ⟨neg_neg_of_pos (inv_pos.mpr (he (phi n))), inv_pos.mpr (he (phi n))⟩)
    (fun n => (by norm_num : (-1 : ℝ) ≤ 0).trans (hu (phi n)).1)
    (fun n => (hu (phi n)).2.trans_lt htheta)
    (fun n => he (phi n)) (fun n => hk (phi n)) (fun n => hclose (phi n))
    (hezero.comp hphi.tendsto_atTop) htime (fun n i j => by
      simpa only [← Prod.zero_eq_mk, add_zero] using hG (phi n) i j)
  have hnormalized : Tendsto (fun n => (1 - u (phi n)) * (DG (phi n)).scalarCurvature 0)
      atTop (𝓝 1) := by
    simpa only [one_div, mul_inv_cancel₀ (sub_pos.mpr huone).ne', Function.comp_def] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub htime).mul hlimit
  have herror : Tendsto (fun n => |(1 - u (phi n)) *
      (DG (phi n)).scalarCurvature 0 - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hnormalized.sub_const 1).abs
  obtain ⟨n, hn⟩ := (herror.eventually (eventually_lt_nhds heta)).exists
  rw [hscalar] at hn
  exact (not_lt_of_ge (hlarge (phi n))) hn

end PoincareConjecture.M35
