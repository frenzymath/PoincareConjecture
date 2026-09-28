import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.Domination
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Equation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Hessian











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric.UniformHarmonicLift

open LeviCivitaData

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem contDiffOn_exhaustionKernel_pullback
    {O : M} {r C A : ℝ} (F : UniformHarmonicLift g O r C A)
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ) (y : M) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => dirichletExhaustionKernel
      (fun q => Dirichlet.heatKernelContinuousTime D (S q)) p.2 (F.e p.1) y)
      (Metric.ball 0 (2 * r) ×ˢ Ioi 0) := by
  have hH := Dirichlet.contMDiffOn_dirichletExhaustionKernel
    D hc hk hRic S hΩmono hcover
  have hs : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : E × ℝ => dirichletExhaustionKernel
        (fun q => Dirichlet.heatKernelContinuousTime D (S q)) p.2 (F.e p.1) y)
      (Metric.ball 0 (2 * r) ×ˢ Ioi 0) := by
    apply hH.comp
      ((contMDiffOn_snd.prodMk
        (F.he.comp contMDiffOn_fst (fun p hp => hp.1))).prodMk contMDiffOn_const)
    intro p hp
    exact ⟨⟨hp.2, mem_univ _⟩, mem_univ _⟩
  simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hs
  exact contMDiffOn_iff_contDiffOn.mp hs


theorem hasDerivAt_exhaustionKernel_pullback
    {O : M} {r C A : ℝ} (F : UniformHarmonicLift g O r C A)
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (y : M) {x : E} (hx : x ∈ Metric.ball 0 (2 * r)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => dirichletExhaustionKernel
      (fun q => Dirichlet.heatKernelContinuousTime D (S q)) s (F.e x) y)
      (∑ i, ∑ j, F.h.inverseCoefficients x i j *
        fderiv ℝ (fderiv ℝ (fun z => dirichletExhaustionKernel
          (fun q => Dirichlet.heatKernelContinuousTime D (S q)) t (F.e z) y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) t := by
  let H := dirichletExhaustionKernel (fun q => Dirichlet.heatKernelContinuousTime D (S q))
  have hH := Dirichlet.contMDiffOn_dirichletExhaustionKernel D hc hk hRic S hΩmono hcover
  have hslice : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => H t z y) := by
    intro z
    have hs := hH.contMDiffAt
      (((isOpen_Ioi.prod isOpen_univ).prod isOpen_univ).mem_nhds
        (show ((t, z), y) ∈ ((Ioi 0 ×ˢ univ) ×ˢ univ) from
          ⟨⟨ht, mem_univ z⟩, mem_univ y⟩))
    have hmap : ContMDiffAt (𝓡 n) ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) ∞
        (fun z : M => ((t, z), y)) z :=
      (contMDiffAt_const.prodMk contMDiffAt_id).prodMk contMDiffAt_const
    have hscomp := hs.comp z hmap
    exact hscomp
  have he := F.he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have hinv : ∀ᶠ z in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) F.e z).IsInvertible := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact F.hlocal z hz
  have hmetric : ∀ᶠ z in 𝓝 x, ∀ v w : TangentSpace (𝓡 n) z,
      F.h.inner z v w = g.inner (F.e z)
        (mfderiv (𝓡 n) (𝓡 n) F.e z v) (mfderiv (𝓡 n) (𝓡 n) F.e z w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz v w
    exact congrArg (fun L => L v w) (F.hpullback z hz)
  have hpull := F.D'.laplacian_comp_of_metric_pullback D he hinv hmetric (hslice (F.e x))
  have hheat := Dirichlet.hasDerivAt_dirichletExhaustionKernel_laplacian
    D hc hk hRic S hΩmono hcover (F.e x) y ht
  change HasDerivAt (fun s => H s (F.e x) y) (D.laplacian (fun z => H t z y) (F.e x)) t at hheat
  rw [← hpull] at hheat
  change HasDerivAt (fun s => H s (F.e x) y)
    (F.D'.laplacian (fun z => H t (F.e z) y) x) t at hheat
  have hcoord : ContDiffAt ℝ ∞ (fun z => H t (F.e z) y) x :=
    contMDiffAt_iff_contDiffAt.mp ((hslice (F.e x)).comp x he)
  rw [F.D'.laplacian_eq_sum_fderiv_of_harmonic hcoord (F.hharmonic x hx)] at hheat
  exact hheat


theorem exists_exhaustionKernel_pullback_bound
    {O : M} {r C A : ℝ} (F : UniformHarmonicLift g O r C A)
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x ∈ Metric.ball (0 : E) (2 * r), ∀ y,
      |dirichletExhaustionKernel (fun q => Dirichlet.heatKernelContinuousTime D (S q))
        t (F.e x) y| ≤ B * dirichletExhaustionKernel
          (fun q => Dirichlet.heatKernelContinuousTime D (S q)) (b + 1) O y := by
  let R := max 1 (Real.sqrt C * (2 * r))
  have hmono := fun (t : ℝ) (ht : 0 < t) x y =>
    D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y
  have hDom := fun q => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S q)
  obtain ⟨B, hB, hb⟩ := D.exists_dirichletExhaustionKernel_later_row_bound
    (NeZero.pos n) hc hk hRic (fun q => (S q).isOpen) hΩmono hcover hDom hmono
    O (R := R) (le_max_left _ _) ha hab
  refine ⟨B, hB, ?_⟩
  intro t ht x hx y
  have hdist : (g.edist O (F.e x)).toReal ≤ R := by
    calc
      _ ≤ Real.sqrt C * ‖x‖ := by
        simpa only [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x))]
          using ENNReal.toReal_mono ENNReal.ofReal_ne_top (F.hdist x hx)
      _ ≤ Real.sqrt C * (2 * r) := mul_le_mul_of_nonneg_left
        (mem_ball_zero_iff.mp hx).le (Real.sqrt_nonneg C)
      _ ≤ R := le_max_right _ _
  have ht0 : 0 < t := ha.trans_le ht.1
  have hn := DirichletExhaustion.nonneg hDom
    (fun s hs z w => D.bddAbove_heatKernelContinuousTime_exhaustion
      (NeZero.pos n) hc hk hRic S hΩmono hcover hs z w) ht0 (F.e x) y
  rw [abs_of_nonneg hn]
  exact hb t ht (F.e x) hdist y

end PoincareConjecture.RiemannianMetric.UniformHarmonicLift
