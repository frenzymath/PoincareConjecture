import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeDisk
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeGreenRectangle
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityRadialIntegral












set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior




theorem coneDisk_green {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : AbsolutelyContinuousOnInterval v (-Real.pi) Real.pi)
    (hper : v (-Real.pi) = v Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hinc : ∀ t ∈ Icc (-Real.pi) Real.pi, ∀ u ∈ Icc (-Real.pi) Real.pi,
      v u - v t = ∫ θ in t..u, d θ)
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    IntegrableOn (fun z => coneDiskField g r v0 v d x i z * test z +
        coneDiskMap g r v0 v x z *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) (closedBall x r) ∧
      (∫ z in closedBall x r, coneDiskField g r v0 v d x i z * test z +
        coneDiskMap g r v0 v x z *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        r * ∫ θ in (-Real.pi)..Real.pi,
          g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hvc : ContinuousOn v (Icc (-Real.pi) Real.pi) := by
    simpa only [uIcc_of_le hπ] using hv.continuousOn
  have hL := coneDisk_memLp hr hρ hK hvc hg h0 hvb hd hD x
  let : IsFiniteMeasure (volume.restrict (closedBall x r)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x r).measure_lt_top.ne
  have h1 : IntegrableOn (coneDiskField g r v0 v d x i) (closedBall x r) :=
    (hL.2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h0L : IntegrableOn (coneDiskMap g r v0 v x) (closedBall x r) :=
    hL.1.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hdt : Continuous (fun z =>
      fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
    (ht.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ⟨(h1.mul_continuousOn ht.continuous.continuousOn (isCompact_closedBall x r)).add
    (h0L.mul_continuousOn hdt.continuousOn (isCompact_closedBall x r)), ?_⟩
  rw [disk_integral_polar]
  calc
    _ = ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
          g (coneCoordinates r v0 v p.1 p.2) *
            fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
      apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      have hpt : p ∈ polarCoord.target := ⟨hp.1.1, hp.2⟩
      simp only [coneDiskField_polar g r v0 v d x i hpt,
        coneDiskMap_polar g r v0 v x hpt]
    _ = ∫ p in Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi,
        p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
          g (coneCoordinates r v0 v p.1 p.2) *
            fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
      setIntegral_congr_set (Measure.set_prod_ae_eq
        (Ioc_ae_eq_Icc (α := ℝ) (μ := volume)) (Ioo_ae_eq_Icc (α := ℝ) (μ := volume)))
    _ = _ := coneGreen_rectangle hr hρ hK hv hper hg h0 hvb hd hinc hD x test ht i

end PoincareConjecture.M65Interior
