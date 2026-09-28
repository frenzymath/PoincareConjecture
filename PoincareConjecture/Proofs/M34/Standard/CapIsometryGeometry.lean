import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter
import PoincareConjecture.Proofs.M13.OrdinaryFlow










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M34

variable {n : ℕ} {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ X]
  (g : RiemannianMetric n M) (h : RiemannianMetric n X)
  (f : Diffeomorph (𝓡 n) (𝓡 n) M X ∞) (hf : MetricHomothety g h f 1)

include hf



theorem metricIsometry_pathELength (γ : ℝ → M) (a b : ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Icc a b)) :
    h.pathELength (f ∘ γ) a b = g.pathELength γ a b := by
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
    M13.homothety_pathELength g h f 1 (by norm_num) hf γ a b hγ



theorem metricIsometry_ball (x : M) (r : ℝ) :
    f '' g.ball x r = h.ball (f x) r := by
  simpa only [Real.sqrt_one, one_mul] using
    M13.homothety_ball_image g h f 1 (by norm_num) hf x r



theorem metricIsometry_volume
    [MeasurableSpace M] [MeasurableSpace X] [BorelSpace M] [BorelSpace X]
    [T3Space M] [T3Space X] (U : Set M) :
    calibratedMetricVolume h (f '' U) = calibratedMetricVolume g U := by
  simpa only [Real.rpow_eq_pow, Real.one_rpow, ENNReal.ofReal_one, one_mul] using
    M13.homothety_volume_image g h f 1 (by norm_num) hf U

end PoincareConjecture.M34

namespace PoincareConjecture.M34

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 X)
  (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1)

include hf



theorem metricIsometry_intrinsicEDist (U : Set M) (x y : M) :
    intrinsicEDist h (f '' U) (f x) (f y) = intrinsicEDist g U x y := by
  apply le_antisymm
  · simpa only [ENNReal.ofReal_one, one_mul] using
      g.intrinsicEDist_image_le_mul h f U (fun z _ => f.contMDiffAt.of_le (by simp))
        (by norm_num : (0 : ℝ) < 1) (fun z _ v => by
          simpa only [Real.sqrt_one] using
            (M13.homothety_tangentNorm g h f 1 (by norm_num) hf z v).le) x y
  · apply le_sInf
    rintro L ⟨η, hη, hη0, hη1, hηU, rfl⟩
    have hη' : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 (f.symm ∘ η) (Icc (0 : ℝ) 1) :=
      (f.symm.contMDiff.of_le (by simp)).comp_contMDiffOn hη
    have himage : (f.symm ∘ η) '' Icc (0 : ℝ) 1 ⊆ U := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨z, hz, heq⟩ := hηU ⟨s, hs, rfl⟩
      simpa only [Function.comp_apply, ← heq, f.symm_apply_apply] using hz
    have hlength := metricIsometry_pathELength g h f hf (f.symm ∘ η) 0 1 hη'
    have heq : f ∘ (f.symm ∘ η) = η := by
      funext s
      exact f.apply_symm_apply (η s)
    rw [heq] at hlength
    rw [hlength]
    exact sInf_le ⟨f.symm ∘ η, hη', by simp [Function.comp_apply, hη0],
      by simp [Function.comp_apply, hη1], himage, rfl⟩



theorem metricIsometry_intrinsicDiameter (U : Set M) :
    intrinsicDiameter h (f '' U) = intrinsicDiameter g U := by
  unfold intrinsicDiameter
  congr 1
  ext L
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨x, hx, hfx⟩ := p.1.property
    obtain ⟨y, hy, hfy⟩ := p.2.property
    refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
    change intrinsicEDist g U x y = intrinsicEDist h (f '' U) p.1.val p.2.val
    rw [← hfx, ← hfy, metricIsometry_intrinsicEDist g h f hf]
  · rintro ⟨p, rfl⟩
    refine ⟨(⟨f p.1, ⟨p.1, p.1.property, rfl⟩⟩,
      ⟨f p.2, ⟨p.2, p.2.property, rfl⟩⟩), ?_⟩
    exact metricIsometry_intrinsicEDist g h f hf U p.1 p.2

end PoincareConjecture.M34
