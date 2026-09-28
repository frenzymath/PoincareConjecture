import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.GramComparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
  {circumference : ℝ} (P : M62.CircleProductData F circumference)

theorem m64CircleProduct_projected_density_le
    (t : ℝ) (f : LoopPlane → P.charts.Point) (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 (n + 1)) f z) :
    m60AreaDensity (F.metric t) (fun w => (f w).1) z ≤
      m60AreaDensity (P.flow.metric t) f z := by
  let := P.charts.chartedSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : P.circle.Point → Type _) :=
    ⟨P.circle.metricOnPoints.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨(P.flow.metric t).toRiemannianMetric⟩
  let hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞
      (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hcomp (i : Fin 2) :
      mfderiv (𝓡 2) (𝓡 n) (fun w => (f w).1) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        (P.charts.split (f z)
          (mfderiv (𝓡 2) (𝓡 (n + 1)) f z
            (EuclideanSpace.basisFun (Fin 2) ℝ i))).1 := by
    have h := mfderiv_comp_apply (f := f) (g := (Prod.fst : P.charts.Point → M))
      z (hfst.mdifferentiableAt (by simp)) hf
        (EuclideanSpace.basisFun (Fin 2) ℝ i)
    rw [P.charts.split_space]
    simpa +instances only [Function.comp_def] using h
  let e (i : Fin 2) : TangentSpace (𝓡 (n + 1)) (f z) :=
    mfderiv (𝓡 2) (𝓡 (n + 1)) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let b00 : ℝ := (F.metric t).inner (f z).1 (P.charts.split (f z) (e 0)).1
      (P.charts.split (f z) (e 0)).1
  let b01 : ℝ := (F.metric t).inner (f z).1 (P.charts.split (f z) (e 0)).1
      (P.charts.split (f z) (e 1)).1
  let b11 : ℝ := (F.metric t).inner (f z).1 (P.charts.split (f z) (e 1)).1
      (P.charts.split (f z) (e 1)).1
  let s00 : ℝ := P.circle.metricOnPoints.inner (f z).2
      (P.charts.split (f z) (e 0)).2 (P.charts.split (f z) (e 0)).2
  let s01 : ℝ := P.circle.metricOnPoints.inner (f z).2
      (P.charts.split (f z) (e 0)).2 (P.charts.split (f z) (e 1)).2
  let s11 : ℝ := P.circle.metricOnPoints.inner (f z).2
      (P.charts.split (f z) (e 1)).2 (P.charts.split (f z) (e 1)).2
  have hb00 : 0 ≤ b00 := by
    exact (F.metric t).toRiemannianMetric.toCore (f z).1 |>.re_inner_nonneg _
  have hb11 : 0 ≤ b11 := by
    exact (F.metric t).toRiemannianMetric.toCore (f z).1 |>.re_inner_nonneg _
  have hs00 : 0 ≤ s00 := by
    exact P.circle.metricOnPoints.toRiemannianMetric.toCore (f z).2 |>.re_inner_nonneg _
  have hs11 : 0 ≤ s11 := by
    exact P.circle.metricOnPoints.toRiemannianMetric.toCore (f z).2 |>.re_inner_nonneg _
  have hbdet : b01 ^ 2 ≤ b00 * b11 := by
    dsimp [b00, b01, b11]
    change (inner ℝ (P.charts.split (f z) (e 0)).1
        (P.charts.split (f z) (e 1)).1) ^ 2 ≤
      inner ℝ (P.charts.split (f z) (e 0)).1
        (P.charts.split (f z) (e 0)).1 *
      inner ℝ (P.charts.split (f z) (e 1)).1
        (P.charts.split (f z) (e 1)).1
    simpa only [pow_two] using real_inner_mul_inner_self_le
      (P.charts.split (f z) (e 0)).1 (P.charts.split (f z) (e 1)).1
  have hsdet : s01 ^ 2 ≤ s00 * s11 := by
    dsimp [s00, s01, s11]
    change (inner ℝ (P.charts.split (f z) (e 0)).2
        (P.charts.split (f z) (e 1)).2) ^ 2 ≤
      inner ℝ (P.charts.split (f z) (e 0)).2
        (P.charts.split (f z) (e 0)).2 *
      inner ℝ (P.charts.split (f z) (e 1)).2
        (P.charts.split (f z) (e 1)).2
    simpa only [pow_two] using real_inner_mul_inner_self_le
      (P.charts.split (f z) (e 0)).2 (P.charts.split (f z) (e 1)).2
  have hB00 : m60AreaGram (F.metric t) (fun w => (f w).1) z 0 0 = b00 := by
    simp only [m60AreaGram]
    change (F.metric t).inner (f z).1
        (mfderiv (𝓡 2) (𝓡 n) (fun w => (f w).1) z
          (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 n) (fun w => (f w).1) z
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = b00
    rw [hcomp 0]
  have hB01 : m60AreaGram (F.metric t) (fun w => (f w).1) z 0 1 = b01 := by
    simp only [m60AreaGram]
    change (F.metric t).inner (f z).1
        (mfderiv (𝓡 2) (𝓡 n) (fun w => (f w).1) z
          (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 n) (fun w => (f w).1) z
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = b01
    rw [hcomp 0, hcomp 1]
  have hB11 : m60AreaGram (F.metric t) (fun w => (f w).1) z 1 1 = b11 := by
    simp only [m60AreaGram]
    change (F.metric t).inner (f z).1
        (mfderiv (𝓡 2) (𝓡 n) (fun w => (f w).1) z
          (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (mfderiv (𝓡 2) (𝓡 n) (fun w => (f w).1) z
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = b11
    rw [hcomp 1]
  have hG00 : m60AreaGram (P.flow.metric t) f z 0 0 = b00 + s00 := by
    simp [m60AreaGram, e, b00, s00, P.metric_eq]
  have hG01 : m60AreaGram (P.flow.metric t) f z 0 1 = b01 + s01 := by
    simp [m60AreaGram, e, b01, s01, P.metric_eq]
  have hG11 : m60AreaGram (P.flow.metric t) f z 1 1 = b11 + s11 := by
    simp [m60AreaGram, e, b11, s11, P.metric_eq]
  have hdet :
      Matrix.det (m60AreaGram (F.metric t) (fun w => (f w).1) z) ≤
        Matrix.det (m60AreaGram (P.flow.metric t) f z) := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    rw [m60AreaGram_symm (F.metric t) (fun w => (f w).1) z 1 0]
    rw [m60AreaGram_symm (P.flow.metric t) f z 1 0]
    rw [hB00, hB11, hB01, hG00, hG11, hG01]
    simpa only [pow_two] using
      (m64_gramDet_add_nonneg hb00 hb11 hs00 hs11 hbdet hsdet)
  unfold m60AreaDensity
  exact Real.sqrt_le_sqrt (max_le_max (le_refl _) hdet)

end PoincareConjecture
