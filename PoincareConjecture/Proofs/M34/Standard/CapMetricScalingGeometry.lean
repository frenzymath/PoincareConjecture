import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M13.OrdinaryFlow











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem scaleSmoothMetric_pathELength (g : RiemannianMetric n M)
    (Q : ℝ) (hQ : 0 < Q) (γ : ℝ → M) (a b : ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Icc a b)) :
    RiemannianMetric.pathELength (scaleSmoothMetric g Q hQ) γ a b =
      ENNReal.ofReal (Real.sqrt Q) * g.pathELength γ a b := by
  simpa only [Diffeomorph.coe_refl, Function.id_comp] using
    homothety_pathELength g (scaleSmoothMetric g Q hQ)
      (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (identity_metricHomothety g Q hQ) γ a b hγ



theorem scaleSmoothMetric_ball (g : RiemannianMetric n M)
    (Q : ℝ) (hQ : 0 < Q) (x : M) (r : ℝ) :
    RiemannianMetric.ball (scaleSmoothMetric g Q hQ) x (Real.sqrt Q * r) = g.ball x r := by
  simpa only [Diffeomorph.coe_refl, id_eq, image_id] using
    (homothety_ball_image g (scaleSmoothMetric g Q hQ)
      (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (identity_metricHomothety g Q hQ) x r).symm



theorem scaleSmoothMetric_volume [T3Space M] [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric n M) (Q : ℝ) (hQ : 0 < Q) (X : Set M) :
    calibratedMetricVolume (scaleSmoothMetric g Q hQ) X =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) * calibratedMetricVolume g X := by
  simpa only [Diffeomorph.coe_refl, image_id] using
    homothety_volume_image g (scaleSmoothMetric g Q hQ)
      (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (identity_metricHomothety g Q hQ) X

end PoincareConjecture.M13

namespace PoincareConjecture.M13

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem scaleSmoothMetric_intrinsicEDist (g : RiemannianMetric 3 M)
    (Q : ℝ) (hQ : 0 < Q) (X : Set M) (x y : M) :
    intrinsicEDist (scaleSmoothMetric g Q hQ) X x y =
      ENNReal.ofReal (Real.sqrt Q) * intrinsicEDist g X x y := by
  let c := ENNReal.ofReal (Real.sqrt Q)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  change intrinsicEDist (scaleSmoothMetric g Q hQ) X x y =
    c * intrinsicEDist g X x y
  apply le_antisymm
  · apply (ENNReal.inv_mul_le_iff hc0 hct).mp
    apply le_sInf
    rintro L ⟨γ, hγ, hγ0, hγ1, hγX, rfl⟩
    have hb : intrinsicEDist (scaleSmoothMetric g Q hQ) X x y ≤
        c * g.pathELength γ 0 1 := by
      rw [← scaleSmoothMetric_pathELength g Q hQ γ 0 1 hγ]
      exact sInf_le ⟨γ, hγ, hγ0, hγ1, hγX, rfl⟩
    calc
      _ ≤ c⁻¹ * (c * g.pathELength γ 0 1) := mul_le_mul_right hb c⁻¹
      _ = _ := ENNReal.inv_mul_cancel_left hc0 hct
  · apply le_sInf
    rintro L ⟨γ, hγ, hγ0, hγ1, hγX, rfl⟩
    rw [scaleSmoothMetric_pathELength g Q hQ γ 0 1 hγ]
    have hb : intrinsicEDist g X x y ≤ g.pathELength γ 0 1 :=
      sInf_le ⟨γ, hγ, hγ0, hγ1, hγX, rfl⟩
    exact mul_le_mul_right hb c



theorem scaleSmoothMetric_intrinsicDiameter (g : RiemannianMetric 3 M)
    (Q : ℝ) (hQ : 0 < Q) (X : Set M) :
    intrinsicDiameter (scaleSmoothMetric g Q hQ) X =
      ENNReal.ofReal (Real.sqrt Q) * intrinsicDiameter g X := by
  change (⨆ p : X × X, intrinsicEDist (scaleSmoothMetric g Q hQ) X p.1 p.2) =
    ENNReal.ofReal (Real.sqrt Q) * ⨆ p : X × X, intrinsicEDist g X p.1 p.2
  simp_rw [scaleSmoothMetric_intrinsicEDist]
  exact (ENNReal.mul_iSup _ _).symm

end PoincareConjecture.M13
