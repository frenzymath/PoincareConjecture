import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RadialLift












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem auxiliaryCircle_radial_mfderiv_split
    (P : M62.CircleProductData F circumference) (delta : ℝ)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (v : LoopPlane) :
    P.charts.split (auxiliaryCircleRadialLift P f delta z)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (auxiliaryCircleRadialLift P f delta) z v) =
      (mfderiv (𝓡 2) (𝓡 n) f z v,
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (delta * z 1) (delta * v 1)) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let phi : LoopPlane → ℝ := fun p => delta * p 1
  let L : LoopPlane →L[ℝ] ℝ := delta • EuclideanSpace.proj 1
  have hphi : HasFDerivAt phi L z := L.hasFDerivAt
  have hc : MDifferentiableAt (𝓡 2) (𝓡 1)
      (fun p => P.circle.quotient (phi p)) z :=
    (P.circle.quotient_smooth.mdifferentiableAt (by simp)).comp z
      hphi.hasMFDerivAt.mdifferentiableAt
  have hgraph : MDifferentiableAt (𝓡 2) (𝓡 (n + 1))
      (auxiliaryCircleRadialLift P f delta) z :=
    (P.charts.from_product_smooth.mdifferentiableAt (by simp)).comp z (hf.prodMk hc)
  apply Prod.ext
  · rw [P.charts.split_space]
    have h := mfderiv_comp_apply (f := auxiliaryCircleRadialLift P f delta)
      (g := (Prod.fst : P.charts.Point → M)) z
      ((contMDiff_fst.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hgraph v
    exact h.symm
  · rw [P.charts.split_circle]
    have h := mfderiv_comp_apply (f := auxiliaryCircleRadialLift P f delta)
      (g := (Prod.snd : P.charts.Point → P.circle.Point)) z
      ((contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hgraph v
    have hq := mfderiv_comp_apply z
      (P.circle.quotient_smooth.mdifferentiableAt (by simp))
      hphi.hasMFDerivAt.mdifferentiableAt v
    rw [hphi.hasMFDerivAt.mfderiv] at hq
    exact h.symm.trans hq



theorem auxiliaryCircle_radial_areaGram
    (P : M62.CircleProductData F circumference) (time delta : ℝ)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (i j : Fin 2) :
    m60AreaGram (P.flow.metric time) (auxiliaryCircleRadialLift P f delta) z i j =
      m60AreaGram (F.metric time) f z i j +
        (delta * (EuclideanSpace.basisFun (Fin 2) ℝ i) 1) *
          (delta * (EuclideanSpace.basisFun (Fin 2) ℝ j) 1) := by
  dsimp only [m60AreaGram]
  rw [P.metric_eq, auxiliaryCircle_radial_mfderiv_split P delta hf,
    auxiliaryCircle_radial_mfderiv_split P delta hf]
  change (F.metric time).inner (f z) _ _ +
    P.circle.metricOnPoints.inner (P.circle.quotient (delta * z 1)) _ _ = _
  erw [P.circle.metric_quotient]



theorem auxiliaryCircle_radial_areaGram_det
    (P : M62.CircleProductData F circumference) (time delta : ℝ)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    (m60AreaGram (P.flow.metric time) (auxiliaryCircleRadialLift P f delta) z).det =
      (m60AreaGram (F.metric time) f z).det +
        delta ^ 2 * m60AreaGram (F.metric time) f z 0 0 := by
  simp only [Matrix.det_fin_two, auxiliaryCircle_radial_areaGram P time delta hf]
  norm_num [EuclideanSpace.basisFun_apply]
  ring



theorem auxiliaryCircle_radial_density_le
    (P : M62.CircleProductData F circumference) (time delta : ℝ)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    m60AreaDensity (P.flow.metric time) (auxiliaryCircleRadialLift P f delta) z ≤
      m60AreaDensity (F.metric time) f z +
        |delta| * Real.sqrt (m60AreaGram (F.metric time) f z 0 0) := by
  have hd := m60AreaGram_det_nonneg (F.metric time) f z
  have h00 := m60AreaGram_diagonal_nonneg (F.metric time) f z 0
  unfold m60AreaDensity
  rw [auxiliaryCircle_radial_areaGram_det P time delta hf,
    max_eq_right (add_nonneg hd (mul_nonneg (sq_nonneg delta) h00)), max_eq_right hd]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [add_sq, mul_pow, Real.sq_sqrt hd, Real.sq_sqrt h00, sq_abs]
  nlinarith [mul_nonneg (Real.sqrt_nonneg ((m60AreaGram (F.metric time) f z).det))
    (mul_nonneg (abs_nonneg delta) (Real.sqrt_nonneg (m60AreaGram (F.metric time) f z 0 0)))]



theorem m60AreaGram_sqrt_diagonal_le_one_add_energy
    (g : RiemannianMetric n M) (f : LoopPlane → M) (z : LoopPlane) :
    Real.sqrt (m60AreaGram g f z 0 0) ≤ 1 + m60EnergyDensity g f z := by
  have h00 := m60AreaGram_diagonal_nonneg g f z 0
  have h11 := m60AreaGram_diagonal_nonneg g f z 1
  rw [m60EnergyDensity, Matrix.trace_fin_two]
  nlinarith [Real.sq_sqrt h00, sq_nonneg (Real.sqrt (m60AreaGram g f z 0 0) - 1)]



theorem auxiliaryCircle_radial_density_le_energy_error
    (P : M62.CircleProductData F circumference) (time delta : ℝ)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    m60AreaDensity (P.flow.metric time) (auxiliaryCircleRadialLift P f delta) z ≤
      m60AreaDensity (F.metric time) f z +
        |delta| * (1 + m60EnergyDensity (F.metric time) f z) := by
  exact (auxiliaryCircle_radial_density_le P time delta hf).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (m60AreaGram_sqrt_diagonal_le_one_add_energy (F.metric time) f z) (abs_nonneg delta)))

end PoincareConjecture.M64
