import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeDisk
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityRadialIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior

private theorem integral_radial_product (f : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ p in Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi, p.1 * f p.2) =
      (r ^ 2 / 2) * ∫ θ in Icc (-Real.pi) Real.pi, f θ := by
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun s : ℝ => s) f]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr,
    integral_id]
  ring

theorem coneDisk_derivativeEnergy_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : EuclideanSpace ℝ (Fin 3) → E}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc (-Real.pi) Real.pi))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) :
    (∫ z in closedBall x r, ∑ i : Fin 2, ‖coneDiskField g r v0 v d x i z‖ ^ 2) ≤
      (K ^ 2 / 2) * ∫ θ in Icc (-Real.pi) Real.pi, (‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc (-Real.pi) Real.pi
  let A (θ : ℝ) := ‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2
  let c := (r⁻¹) ^ 2 * K ^ 2
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hA : IntegrableOn A (Icc (-Real.pi) Real.pi) :=
    (((hv.sub continuousOn_const).norm.pow 2).integrableOn_compact isCompact_Icc).add
      ((memLp_two_iff_integrable_sq_norm hd.1).mp hd)
  have hfields : IntegrableOn
      (fun p : ℝ × ℝ => ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2) S := by
    apply integrable_finsetSum
    intro i _
    have hi := coneCartesianField_memLp hr hρ hK hv hg h0 hvb hd hD i
    exact (memLp_two_iff_integrable_sq_norm hi.1).mp hi
  have hweighted : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2) S :=
    IntegrableOn.continuousOn_mul continuous_fst.continuousOn hfields hS
  have hmajor : IntegrableOn (fun p : ℝ × ℝ => p.1 * (c * A p.2)) S := by
    have hrad : IntegrableOn (fun s : ℝ => s) (Icc (0 : ℝ) r) :=
      continuous_id.continuousOn.integrableOn_compact isCompact_Icc
    have h := hrad.mul_prod (hA.const_mul c)
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have hbound : (∫ p in S,
      p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2) ≤
        ∫ p in S, p.1 * (c * A p.2) := by
    apply integral_mono_ae hweighted hmajor
    filter_upwards [ae_restrict_mem hS.measurableSet] with p hp
    exact mul_le_mul_of_nonneg_left
      (coneCartesianField_norm_sq_le g r v0 v d p.1 p.2
        (hD _ (coneCoordinates_mem_closedBall hr h0 (hvb hp.2) hp.1))) hp.1.1
  have hmajorEq : (∫ p in S, p.1 * (c * A p.2)) =
      (K ^ 2 / 2) * ∫ θ in Icc (-Real.pi) Real.pi, A θ := by
    calc
      _ = c * ∫ p in S, p.1 * A p.2 := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun p => by ring
      _ = c * ((r ^ 2 / 2) * ∫ θ in Icc (-Real.pi) Real.pi, A θ) := by
        rw [integral_radial_product A hr.le]
      _ = _ := by
        dsimp only [c]
        field_simp
  rw [disk_integral_polar]
  calc
    _ = ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2 := by
      apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      have hpt : p ∈ polarCoord.target := ⟨hp.1.1, hp.2⟩
      simp only [coneDiskField_polar g r v0 v d x _ hpt]
    _ = ∫ p in S,
        p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2 :=
      setIntegral_congr_set (Measure.set_prod_ae_eq
        (Ioc_ae_eq_Icc (α := ℝ) (μ := volume)) (Ioo_ae_eq_Icc (α := ℝ) (μ := volume)))
    _ ≤ _ := hbound.trans_eq hmajorEq

end PoincareConjecture.M65Interior
