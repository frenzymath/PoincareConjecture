import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.TargetChartEstimate









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}




theorem m60HarmonicChart_laplacian_lower (D : LeviCivitaData g)
    (b : M) {φ : LoopPlane → M} {a : LoopPlane → ℝ} {O : Set LoopPlane}
    {p : LoopPlane} (hO : IsOpen O) (hp : p ∈ O) (d e : LoopPlane)
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ O)
    (hchart : ∀ q ∈ O, φ q ∈ (extChartAt (𝓡 n) b).source)
    (hharm :
      let c := extChartAt (𝓡 n) b
      let v := c ∘ φ
      let B := g.pullbackCoefficients c.symm
      ∀ q ∈ O,
        covDerivAlong (christoffelBilinear B) v (fun r => fderiv ℝ v r d) d q +
          covDerivAlong (christoffelBilinear B) v (fun r => fderiv ℝ v r e) e q = 0)
    (hdd : ∀ q ∈ O, g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q d)
      (mfderiv (𝓡 2) (𝓡 n) φ q d) = a q) :
    -2 * D.curvatureTensor (φ p) (mfderiv (𝓡 2) (𝓡 n) φ p d)
      (mfderiv (𝓡 2) (𝓡 n) φ p e) (mfderiv (𝓡 2) (𝓡 n) φ p d)
      (mfderiv (𝓡 2) (𝓡 n) φ p e) ≤
      fderiv ℝ (fun q => fderiv ℝ a q d) p d +
        fderiv ℝ (fun q => fderiv ℝ a q e) p e := by
  let c := extChartAt (𝓡 n) b
  let v := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  let Γ := christoffelBilinear B
  have hφq (q : LoopPlane) (hq : q ∈ O) : ContMDiffAt (𝓡 2) (𝓡 n) ∞ φ q :=
    hφ.contMDiffAt (hO.mem_nhds hq)
  have hc (q : LoopPlane) (hq : q ∈ O) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ q) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hchart q hq)
  have hv : ContDiffOn ℝ ∞ v O := by
    intro q hq
    exact (contMDiffAt_iff_contDiffAt.mp ((hc q hq).comp q (hφq q hq))).contDiffWithinAt
  have hdv (q : LoopPlane) (hq : q ∈ O) (w : LoopPlane) :
      fderiv ℝ v q w = mfderiv (𝓡 n) (𝓡 n) c (φ q)
        (mfderiv (𝓡 2) (𝓡 n) φ q w) := by
    have h := mfderiv_comp q ((hc q hq).mdifferentiableAt (by simp))
      ((hφq q hq).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun L => L w) h
  have hpair (q : LoopPlane) (hq : q ∈ O) (w z : LoopPlane) :
      B (v q) (fderiv ℝ v q w) (fderiv ℝ v q z) =
        g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q w) (mfderiv (𝓡 2) (𝓡 n) φ q z) := by
    rw [hdv q hq w, hdv q hq z]
    exact chartCoefficients_apply g b (hchart q hq) _ _
  have hBq (q : LoopPlane) (hq : q ∈ O) : ContDiffAt ℝ ∞ B (v q) :=
    (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source (hchart q hq)))
  have hΓ (q : LoopPlane) (hq : q ∈ O) : ContDiffAt ℝ ∞ Γ (v q) :=
    contDiffAt_christoffelBilinear (hBq q hq)
      (g.isInvertible_chartCoefficients b (c.map_source (hchart q hq)))
  have hG : ContDiffOn ℝ ∞ (fun q => B (v q)) O := by
    intro q hq
    exact ((hBq q hq).comp q (hv.contDiffAt (hO.mem_nhds hq))).contDiffWithinAt
  have hcompat (q : LoopPlane) (hq : q ∈ O) (w : LoopPlane)
      (y z : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun r => B (v r) y z) q w =
        B (v q) (Γ (v q) (fderiv ℝ v q w) y) z +
          B (v q) y (Γ (v q) (fderiv ℝ v q w) z) := by
    have hBd := (hBq q hq).differentiableAt (by simp)
    have hvd := (hv.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
    have hd := ((hBd.hasFDerivAt.comp q hvd.hasFDerivAt).clm_apply
      (hasFDerivAt_const y q)).clm_apply (hasFDerivAt_const z q)
    dsimp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
    exact isMetricCompatibleAt_chartCoefficients g b (c.map_source (hchart q hq)) _ _ _
  have hnonneg (w : EuclideanSpace ℝ (Fin n)) : 0 ≤ B (v p) w w := by
    change 0 ≤ g.inner (c.symm (v p)) (mfderiv (𝓡 n) (𝓡 n) c.symm (v p) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (v p) w)
    by_cases hw : mfderiv (𝓡 n) (𝓡 n) c.symm (v p) w = 0
    · rw [hw]
      simp
    · exact (g.pos _ _ hw).le
  have hb := M60.harmonic_map_metric_bochner hO hp d e hv hG hΓ hcompat
    (fun _ _ => g.symm _ _ _)
    (fun q _ => christoffelBilinear_chart_symm g b (v q)) hharm
    (fun q hq => (hpair q hq d d).trans (hdd q hq))
  have hskew : christoffelCurvature Γ (v p) (fderiv ℝ v p e)
      (fderiv ℝ v p d) (fderiv ℝ v p e) =
      -christoffelCurvature Γ (v p) (fderiv ℝ v p d)
        (fderiv ℝ v p e) (fderiv ℝ v p e) := by
    simp only [christoffelCurvature]
    abel
  rw [hskew, map_neg, neg_apply] at hb
  have hR : B (v p) (christoffelCurvature Γ (v p) (fderiv ℝ v p d)
      (fderiv ℝ v p e) (fderiv ℝ v p e)) (fderiv ℝ v p d) =
      D.curvatureTensor (φ p) (mfderiv (𝓡 2) (𝓡 n) φ p d)
        (mfderiv (𝓡 2) (𝓡 n) φ p e) (mfderiv (𝓡 2) (𝓡 n) φ p d)
        (mfderiv (𝓡 2) (𝓡 n) φ p e) := by
    rw [← coordinateCurvature_eq_christoffelCurvature ((hΓ p hp).differentiableAt (by simp))]
    rw [hdv p hp d, hdv p hp e]
    erw [coordinateCurvature_in_chart g D b (hchart p hp)]
    exact chartCoefficients_apply g b (hchart p hp) _ _
  rw [hR] at hb
  have h0 := hnonneg (covDerivAlong Γ v (fun q => fderiv ℝ v q d) d p)
  have h1 := hnonneg (covDerivAlong Γ v (fun q => fderiv ℝ v q d) e p)
  linarith

end PoincareConjecture
