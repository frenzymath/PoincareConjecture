import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_EmbeddedCollar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryParameters













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_inward_unit_normal_unique
    (N : IntrinsicAnnulus) {a : ℝ} {v w : AnnulusCoordinates}
    (hvunit : N.metric.inner (intrinsicAnnulusBoundary 1 a) v v = 1)
    (hwunit : N.metric.inner (intrinsicAnnulusBoundary 1 a) w w = 1)
    (hvorth : N.metric.inner (intrinsicAnnulusBoundary 1 a) v
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0)
    (hworth : N.metric.inner (intrinsicAnnulusBoundary 1 a) w
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0)
    (hvin : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) v)
    (hwin : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) w) : v = w := by
  let p := intrinsicAnnulusBoundary 1 a
  let T : AnnulusCoordinates := curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a
  change N.metric.inner p v v = 1 at hvunit
  change N.metric.inner p w w = 1 at hwunit
  change N.metric.inner p v T = 0 at hvorth
  change N.metric.inner p w T = 0 at hworth
  have hTT : 0 < N.metric.inner p T T :=
    Real.sqrt_pos.mp (m64Intrinsic_boundarySpeed_pos N (by norm_num) a)
  have hTv : N.metric.inner p T v = 0 := by
    rw [N.metric.symm]
    exact hvorth
  let L : (ℝ × ℝ) →ₗ[ℝ] AnnulusCoordinates :=
    { toFun := fun z => z.1 • T + z.2 • v
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
      map_smul' := by intros; simp [smul_add, mul_smul] }
  have hL (z : ℝ × ℝ) : L z = z.1 • T + z.2 • v := rfl
  have hLi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro z hz
    have hx := congrArg (fun q => N.metric.inner p q T) hz
    have hy := congrArg (fun q => N.metric.inner p q v) hz
    rw [hL] at hx hy
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hvorth, mul_zero, add_zero, map_zero, zero_apply] at hx
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hTv, hvunit, mul_zero, zero_add, mul_one, map_zero, zero_apply] at hy
    exact Prod.ext ((mul_eq_zero.mp hx).resolve_right hTT.ne') hy
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ AnnulusCoordinates := by
    simp
  obtain ⟨z, hz⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLi w
  have hx := congrArg (fun q => N.metric.inner p q T) hz
  rw [hL] at hx
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    hvorth, hworth, mul_zero, add_zero] at hx
  have hx0 : z.1 = 0 := (mul_eq_zero.mp hx).resolve_right hTT.ne'
  have hw : w = z.2 • v := by simpa only [hL, hx0, zero_smul, zero_add] using hz.symm
  have hunit : z.2 ^ 2 = 1 := by
    rw [hw] at hwunit
    simpa only [map_smul, smul_apply, smul_eq_mul, hvunit, mul_one, pow_two] using hwunit
  have hpos : 0 < z.2 := by
    rw [hw, inner_smul_right] at hwin
    exact (mul_pos_iff_of_pos_right hvin).mp hwin
  have hz1 : z.2 = 1 := by nlinarith
  simpa only [hz1, one_smul] using hw.symm



theorem m64Intrinsic_inward_normal_periodic
    (N : IntrinsicAnnulus) {normal : ℝ → AnnulusCoordinates}
    (hnormal : ∀ a,
      N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
      N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
        (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
      0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) :
    Function.Periodic normal rampPeriod := by
  intro a
  have hb := m64Intrinsic_boundary_periodic 1 a
  have hT : curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) (a + rampPeriod) =
      curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a := by
    rw [m64Intrinsic_boundary_velocity, m64Intrinsic_boundary_velocity]
    simp only [rampPeriod, Real.sin_add_two_pi, Real.cos_add_two_pi]
  obtain ⟨hu, ho, hi⟩ := hnormal (a + rampPeriod)
  rw [hb] at hu ho hi
  rw [hT] at ho
  exact m64Intrinsic_inward_unit_normal_unique N hu (hnormal a).1 ho
    (hnormal a).2.1 hi (hnormal a).2.2



theorem m64Intrinsic_normal_map_periodic
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {normal : ℝ → AnnulusCoordinates} {u : ℝ × ℝ → AnnulusCoordinates}
    (hnormal : Function.Periodic normal rampPeriod)
    (hboundary : ∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a)
    (hvelocity : ∀ a, HasDerivAt (fun t => u (a, t)) (normal a) 0)
    (hgeo : ∀ a, G.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Function.Periodic (fun a => u (a, t)) rampPeriod := by
  intro a
  have hinit : u (a + rampPeriod, 0) = u (a, 0) := by
    rw [hboundary, hboundary, m64Intrinsic_boundary_periodic 1 a]
  have hvel : deriv (fun s => extChartAt (𝓡 2)
      (u (a + rampPeriod, 0)) (u (a + rampPeriod, s))) 0 =
      deriv (fun s => extChartAt (𝓡 2) (u (a + rampPeriod, 0)) (u (a, s))) 0 := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq,
      (hvelocity (a + rampPeriod)).deriv, (hvelocity a).deriv] using hnormal a
  have heq := (hgeo (a + rampPeriod)).eq_nhds_on_of_initial_data (hgeo a)
    (convex_Icc (0 : ℝ) 1).isPreconnected (t₀ := 0) (by simp)
    (u (a + rampPeriod, 0)) (by simp) hinit hvel
  exact (heq t ht).self_of_nhds

end PoincareConjecture
