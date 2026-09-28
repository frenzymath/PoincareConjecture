import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ClosedRectanglePhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ProductCircleEnergy













set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem local_circle_phase_column_sq_le_gram
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (f : LoopPlane → P.charts.Point) (L : LoopPlane → ℝ) (p : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 (n + 1)) f p)
    (hL : DifferentiableAt ℝ L p)
    (hquot : P.circle.quotient ∘ L =ᶠ[𝓝 p] Prod.snd ∘ f) (i : Fin 2) :
    (fderiv ℝ L p (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2 ≤
      m60AreaGram (P.flow.metric t) f p i i := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let v : LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ i
  let W := mfderiv (𝓡 2) (𝓡 (n + 1)) f p v
  have hsnd : MDifferentiable (𝓡 (n + 1)) (𝓡 1)
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiable (by simp)
  have hpr := mfderiv_comp_apply (f := f)
    (g := (Prod.snd : P.charts.Point → P.circle.Point)) p (hsnd (f p)) hf v
  have hl := mfderiv_comp_apply (f := L) (g := P.circle.quotient) p
    (P.circle.quotient_smooth.mdifferentiableAt (by simp))
    hL.hasFDerivAt.hasMFDerivAt.mdifferentiableAt v
  rw [hquot.mfderiv_eq, mfderiv_eq_fderiv] at hl
  have hv : (P.charts.split (f p) W).2 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (L p) (fderiv ℝ L p v) := by
    rw [P.charts.split_circle]
    exact hpr.symm.trans hl
  have hpoint : P.circle.quotient (L p) = (f p).2 := hquot.eq_of_nhds
  have hcircle : P.circle.metricOnPoints.inner (f p).2
      (P.charts.split (f p) W).2 (P.charts.split (f p) W).2 = (fderiv ℝ L p v) ^ 2 := by
    rw [hv, ← hpoint]
    simpa +instances only [M62.CircleGeometry.quotient, M62.CircleGeometry.metricOnPoints,
      pow_two] using! P.circle.metric_quotient (L p) (fderiv ℝ L p v) (fderiv ℝ L p v)
  have hbase : 0 ≤ (F.metric t).inner (f p).1
      (P.charts.split (f p) W).1 (P.charts.split (f p) W).1 :=
    (F.metric t).toRiemannianMetric.toCore (f p).1 |>.re_inner_nonneg _
  change (fderiv ℝ L p v) ^ 2 ≤ (P.flow.metric t).inner (f p) W W
  rw [P.metric_eq, hcircle]
  linarith




theorem annulus_exists_continuous_phase_with_gradient_bound
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map (interior m64AnnulusDomain))
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x ∈ Icc (0 : ℝ) curvePeriod, P.circle.quotient (L0 x) = (c0 x).2) :
    ∃ L : LoopPlane → ℝ, Continuous L ∧
      ContDiffOn ℝ 1 L (interior m64AnnulusDomain) ∧
      (∀ p ∈ m64AnnulusDomain, P.circle.quotient (L p) = (A.map p).2) ∧
      (∀ x ∈ Icc (0 : ℝ) curvePeriod, L (annulusPoint x 0) = L0 x) ∧
      ∀ p ∈ interior m64AnnulusDomain, ∀ i : Fin 2,
        (fderiv ℝ L p (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2 ≤
          m60AreaGram (P.flow.metric t) A.map p i i := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) 1
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).of_le (by simp)
  obtain ⟨L, hL, hL1, hq, hb⟩ := closed_rectangle_exists_circle_phase P.circle
    (fun p => (A.map p).2) (hsnd.continuous.comp_continuousOn A.continuous_on_domain)
    (hsnd.comp_contMDiffOn hA) L0 hL0 (fun x hx => by rw [A.lower_boundary]; exact hzero x hx)
  refine ⟨L, hL, hL1, hq, hb, ?_⟩
  intro p hp i
  apply local_circle_phase_column_sq_le_gram P t A.map L p
    (((hA p hp).contMDiffAt (isOpen_interior.mem_nhds hp)).mdifferentiableAt one_ne_zero)
    (((hL1 p hp).contDiffAt (isOpen_interior.mem_nhds hp)).differentiableAt one_ne_zero) _ i
  filter_upwards [isOpen_interior.mem_nhds hp] with q hq'
  exact hq q (interior_subset hq')

end PoincareConjecture.M64
