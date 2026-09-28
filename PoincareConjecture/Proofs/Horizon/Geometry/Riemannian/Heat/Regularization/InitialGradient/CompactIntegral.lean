import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.ParametricIntegral











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace Poincare.Analysis.Heat

variable {d : ℕ} {M E F : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  [IsManifold (𝓡 d) ∞ M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem contMDiffOn_fderiv_parameter {U : Set E} (hU : IsOpen U)
    {f : E × M → F}
    (hf : ContMDiffOn (𝓘(ℝ, E).prod (𝓡 d)) 𝓘(ℝ, F) ∞ f (U ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, E).prod (𝓡 d)) 𝓘(ℝ, E →L[ℝ] F) ∞
      (fun p => fderiv ℝ (fun z => f (z, p.2)) p.1) (U ×ˢ univ) := by
  intro p hp
  let c := chartAt (EuclideanSpace ℝ (Fin d)) p.2
  have hc : p.2 ∈ c.source := mem_chart_source _ _
  have hci : ContMDiffAt (𝓡 d) (𝓡 d) ∞ c.symm (c p.2) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds (c.map_source hc))
  have hcc : ContMDiffAt (𝓡 d) (𝓡 d) ∞ c p.2 :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hc)
  have hfs : ContDiffAt ℝ ∞
      (fun q : (E × EuclideanSpace ℝ (Fin d)) × E => f (q.2, c.symm q.1.2))
      ((p.1, c p.2), p.1) := by
    have htarget : ContMDiffAt (𝓘(ℝ, E).prod (𝓡 d)) 𝓘(ℝ, F) ∞ f
        (p.1, c.symm (c p.2)) := by
      simpa only [c.left_inv hc] using
        hf.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hp)
    have hmap : ContMDiffAt 𝓘(ℝ, (E × EuclideanSpace ℝ (Fin d)) × E)
        (𝓘(ℝ, E).prod (𝓡 d)) ∞
        (fun q => (q.2, c.symm q.1.2)) ((p.1, c p.2), p.1) :=
      contDiffAt_snd.contMDiffAt.prodMk
        (hci.comp ((p.1, c p.2), p.1) contDiffAt_fst.snd.contMDiffAt)
    have h := htarget.comp ((p.1, c p.2), p.1) hmap
    simpa only [Function.comp_def, c.left_inv hc] using h.contDiffAt
  have hd := hfs.fderiv (f := fun q z => f (z, c.symm q.2))
    (g := fun q => q.1) (x₀ := (p.1, c p.2)) contDiffAt_fst (by simp : ∞ + 1 ≤ ∞)
  have h := hd.contMDiffAt.comp p (contMDiffAt_fst.prodMk_space
    (hcc.comp p contMDiffAt_snd))
  apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(continuous_snd.tendsto p) (c.open_source.mem_nhds hc)] with q hq
  simp only [Function.comp_def, c.left_inv hq]


theorem contMDiffOn_iteratedFDeriv_parameter {U : Set E} (hU : IsOpen U)
    {f : E × M → F}
    (hf : ContMDiffOn (𝓘(ℝ, E).prod (𝓡 d)) 𝓘(ℝ, F) ∞ f (U ×ˢ univ))
    (m : ℕ) :
    ContMDiffOn (𝓘(ℝ, E).prod (𝓡 d)) 𝓘(ℝ, E [×m]→L[ℝ] F) ∞
      (fun p => iteratedFDeriv ℝ m (fun z => f (z, p.2)) p.1) (U ×ˢ univ) := by
  induction m with
  | zero =>
    convert (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff.contMDiff.comp_contMDiffOn hf using 1
    all_goals rfl
  | succ m ih =>
    have h := contMDiffOn_fderiv_parameter hU ih
    convert (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).symm.toContinuousLinearEquiv.contDiff.contMDiff.comp_contMDiffOn h using 1
    all_goals rfl


theorem contDiffOn_integral_compact [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [SecondCountableTopology M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {μ : Measure M} [IsFiniteMeasureOnCompacts μ]
    {U : Set E} (hU : IsOpen U) {f : E × M → F}
    (hf : ContMDiffOn (𝓘(ℝ, E).prod (𝓡 d)) 𝓘(ℝ, F) ∞ f (U ×ˢ univ))
    {K : Set M} (hK : IsCompact K) :
    ContDiffOn ℝ ∞ (fun x => ∫ y in K, f (x, y) ∂μ) U := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := μ)⟩
  apply (contDiffOn_integral_of_locally_dominated_iteratedFDeriv hU _ _ _).1
  · exact ae_of_all _ (fun y x hx =>
      (((hf.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ y⟩)).comp x
        (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt).contDiffWithinAt)
  · intro m x hx
    have hj := (contMDiffOn_iteratedFDeriv_parameter hU hf m).continuousOn
    have hc : Continuous (fun y => iteratedFDeriv ℝ m (fun z => f (z, y)) x) :=
      continuous_iff_continuousAt.mpr (fun y =>
        (hj.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ y⟩)).comp
          (continuous_const.prodMk continuous_id).continuousAt)
    exact hc.aestronglyMeasurable
  · intro x hx m
    obtain ⟨V, hVc, hxV, hVU⟩ := exists_compact_subset hU hx
    have hj := (contMDiffOn_iteratedFDeriv_parameter hU hf m).continuousOn
    obtain ⟨C, hC⟩ := (hVc.prod hK).exists_bound_of_continuousOn
      (hj.mono (prod_mono hVU (subset_univ K)))
    refine ⟨V, mem_interior_iff_mem_nhds.mp hxV,
      fun _ => C, integrable_const C, ?_⟩
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    intro z hz
    exact hC (z, y) ⟨hz, hy⟩

end Poincare.Analysis.Heat

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)



theorem contMDiffOn_dirichletExhaustionKernel_integral
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (huc : HasCompactSupport u) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∫ y, u y * dirichletExhaustionKernel
        (fun q => heatKernelContinuousTime D (S q)) p.1 p.2 y ∂g.volumeMeasure)
      (Ioi 0 ×ˢ univ) := by
  let : SecondCountableTopology M := g.secondCountableTopology
  let H := dirichletExhaustionKernel (fun q => heatKernelContinuousTime D (S q))
  have hH := contMDiffOn_dirichletExhaustionKernel D hc hk hRic S hΩmono hcover
  intro p hp
  let c := chartAt E p.2
  have hx : p.2 ∈ c.source := mem_chart_source E p.2
  have hz : (p.1, c p.2) ∈ Ioi 0 ×ˢ c.target := ⟨hp.1, c.map_source hx⟩
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ c.target) := isOpen_Ioi.prod c.open_target
  have hf : ContMDiffOn (𝓘(ℝ, ℝ × E).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : (ℝ × E) × M => u z.2 * H z.1.1 (c.symm z.1.2) z.2)
      ((Ioi 0 ×ˢ c.target) ×ˢ univ) := by
    intro z hz
    have hci : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z.1.2 :=
      contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hz.1.2)
    have ht : ContMDiffAt (𝓘(ℝ, ℝ × E).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun w : (ℝ × E) × M => w.1.1) z :=
      contDiffAt_fst.contMDiffAt.comp z contMDiffAt_fst
    have hx' : ContMDiffAt (𝓘(ℝ, ℝ × E).prod (𝓡 n)) (𝓡 n) ∞
        (fun w : (ℝ × E) × M => w.1.2) z :=
      contDiffAt_snd.contMDiffAt.comp z contMDiffAt_fst
    have hm := (ht.prodMk (hci.comp z hx')).prodMk contMDiffAt_snd
    have hHs := hH.contMDiffAt
      (((isOpen_Ioi.prod isOpen_univ).prod isOpen_univ).mem_nhds
        (show ((z.1.1, c.symm z.1.2), z.2) ∈ ((Ioi 0 ×ˢ univ) ×ˢ univ) from
          ⟨⟨hz.1.1, mem_univ _⟩, mem_univ _⟩))
    exact (((hu z.2).comp z contMDiffAt_snd).mul (hHs.comp z hm)).contMDiffWithinAt
  have hi := Poincare.Analysis.Heat.contDiffOn_integral_compact hU hf huc
    (μ := g.volumeMeasure)
  have hic := (hi.contDiffAt (hU.mem_nhds hz)).contMDiffAt
  have hcc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c p.2 :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hx)
  have h := hic.comp p (contMDiffAt_fst.prodMk_space (hcc.comp p contMDiffAt_snd))
  apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(continuous_snd.tendsto p) (c.open_source.mem_nhds hx)] with z hz
  dsimp only [Function.comp_def]
  rw [c.left_inv hz]
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ (tsupport u))
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport hy.2, zero_mul]

end PoincareConjecture.LeviCivitaData.Dirichlet
