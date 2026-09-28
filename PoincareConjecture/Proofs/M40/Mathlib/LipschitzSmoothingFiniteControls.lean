import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingLocal
import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingPatchEstimate
import PoincareConjecture.Proofs.M40.Mathlib.CompactChartMargin

set_option autoImplicit false

open Function Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

namespace PoincareConjecture.M40

variable {ι X N E F : Type*} [Finite ι]
  [PseudoMetricSpace X] [PseudoEMetricSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace ℝ (V i)] [∀ i, CompleteSpace (V i)]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem exists_convolution_finite_chart_controls
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (a : X → E) (ha : ∀ i, ContinuousOn a (K i))
    {f : E → F} (hf : UniformContinuous f)
    (h : OpenPartialHomeomorph N F) (B : ∀ i, F ≃L[ℝ] V i)
    (W : ∀ i, Set (V i)) (hW : ∀ i, IsOpen (W i))
    (hrange : ∀ i, MapsTo (fun x => B i (f (a x))) (K i) (W i))
    {ρ : X → ℝ} (hρrange : ∀ x, ρ x ∈ Icc 0 1)
    {L A δ C : ι → ℝ≥0} (hδ : ∀ i, 0 < δ i)
    (hρ : ∀ i, LipschitzOnWith (A i) ρ (K i))
    (hinverse : ∀ i,
      LipschitzOnWith (C i) (fun v => h.symm ((B i).symm v)) (W i))
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hbound : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ t ∈ ball (0 : E) R,
      dist (B i (f (a x - t))) (B i (f (a y - t))) ≤ (L i : ℝ) * dist x y) :
    ∃ φ : ContDiffBump (0 : E), φ.rOut < R ∧
      ContDiff ℝ ∞ (normalizedConvolution μ φ f) ∧
      (∀ x, dist (normalizedConvolution μ φ f x) (f x) < ε) ∧
      (∀ i, ∀ x ∈ K i,
        dist (B i (normalizedConvolution μ φ f (a x))) (B i (f (a x))) < δ i) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
        MapsTo (fun x => B i (cutoffBlend (fun y => t * ρ y)
          (fun y => f (a y)) (fun y => normalizedConvolution μ φ f (a y)) x))
          (K i) (W i)) ∧
      ∀ i, LipschitzOnWith (C i * (L i + A i * δ i))
        (fun x => h.symm (cutoffBlend ρ (fun y => f (a y))
          (fun y => normalizedConvolution μ φ f (a y)) x)) (K i) := by
  obtain ⟨d, hd, hmargin⟩ :=
    PoincareConjecture.Proofs.M40.exists_pos_uniform_mapsTo_of_edist_lt K
      (fun i => (B i) ⁻¹' W i) (fun x => f (a x)) hK
      (fun i => (hW i).preimage (B i).continuous)
      (fun i => hf.continuous.comp_continuousOn (ha i)) hrange
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r < min ε d :=
    eventually_lt_nhds (lt_min hε hd)
  have hscale : ∀ᶠ r : ℝ in 𝓝 0,
      ∀ i, ‖(B i).toContinuousLinearMap‖ * r < (δ i : ℝ) := by
    apply eventually_all.mpr
    intro i
    exact (continuousAt_const.mul continuousAt_id).eventually_lt continuousAt_const
      (by simpa using (show (0 : ℝ) < δ i from hδ i))
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hsmall' : ∀ᶠ r : ℝ in 𝓝[>] 0, r < min ε d := nhdsWithin_le_nhds hsmall
  have hscale' : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ i, ‖(B i).toContinuousLinearMap‖ * r < (δ i : ℝ) := nhdsWithin_le_nhds hscale
  obtain ⟨r, hr, hrsmall, hrscale⟩ := (hpos.and (hsmall'.and hscale')).exists
  obtain ⟨φ, hφ, hφsmooth, hφclose⟩ :=
    exists_small_normalizedConvolution_uniform (μ := μ) hf hr hR
  let H : ℝ → X → F := fun t => cutoffBlend (fun y => t * ρ y)
    (fun y => f (a y)) (fun y => normalizedConvolution μ φ f (a y))
  have hHclose (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : X) :
      dist (H t x) (f (a x)) < d :=
    (cutoffBlend_dist_le (ρ := fun y : X => t * ρ y)
      (f := fun y => f (a y)) (g := fun y => normalizedConvolution μ φ f (a y))
      (x := x) (show t * ρ x ∈ Icc (0 : ℝ) 1 from
      ⟨mul_nonneg ht.1 (hρrange x).1,
        (mul_le_mul ht.2 (hρrange x).2 (hρrange x).1 zero_le_one).trans_eq (one_mul 1)⟩)
      (hφclose (a x)).le).trans_lt
      (hrsmall.trans_le (min_le_right _ _))
  have hHrange (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∀ i, MapsTo (H t) (K i) ((B i) ⁻¹' W i) := by
    apply hmargin (H t)
    intro x
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hd).mpr (hHclose t ht x)
  have hφBclose (i : ι) (x : X) :
      dist (B i (normalizedConvolution μ φ f (a x))) (B i (f (a x))) < δ i := by
    calc
      dist (B i (normalizedConvolution μ φ f (a x))) (B i (f (a x)))
          ≤ ‖(B i).toContinuousLinearMap‖ *
              dist (normalizedConvolution μ φ f (a x)) (f (a x)) :=
        (B i).toContinuousLinearMap.lipschitz.dist_le_mul _ _
      _ ≤ ‖(B i).toContinuousLinearMap‖ * r :=
        mul_le_mul_of_nonneg_left (hφclose (a x)).le (norm_nonneg _)
      _ < δ i := hrscale i
  refine ⟨φ, hφ, hφsmooth,
    fun x => (hφclose x).trans (hrsmall.trans_le (min_le_left _ _)),
    fun i x _ => hφBclose i x, hHrange, ?_⟩
  intro i
  apply chartConvolutionBlend_lipschitzOn h (B i) φ a
    hf.continuous.locallyIntegrable (fun _ _ => rfl)
    (fun x hx y hy t ht => hbound i x hx y hy t (ht.trans hφ))
    (hρ i) (fun x _ => hρrange x) (fun x _ => (hφBclose i x).le) (hinverse i) ?_
  intro x hx
  simpa only [H, cutoffBlend, one_mul, mem_preimage] using
    hHrange 1 ⟨zero_le_one, le_rfl⟩ i hx

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem exists_finite_chart_translation_radius
    (e : OpenPartialHomeomorph X E) (K O : ι → Set X)
    (hK : ∀ i, IsCompact (K i)) (hO : ∀ i, IsOpen (O i))
    (hKO : ∀ i, K i ⊆ O i) (hOe : ∀ i, O i ⊆ e.source) :
    ∃ R : ℝ, 0 < R ∧ ∀ i, ∀ x ∈ K i, ∀ t ∈ ball (0 : E) R,
      e x - t ∈ e.target ∧ e.symm (e x - t) ∈ O i := by
  obtain ⟨R, hR, hmargin⟩ :=
    PoincareConjecture.Proofs.M40.exists_pos_uniform_mapsTo_of_edist_lt K
      (fun i => e.target ∩ e.symm ⁻¹' O i) e hK
      (fun i => e.isOpen_inter_preimage_symm (hO i))
      (fun i => e.continuousOn.mono ((hKO i).trans (hOe i)))
      (fun i x hx => ⟨e.map_source (hOe i (hKO i hx)), by
        simpa only [mem_preimage, e.left_inv (hOe i (hKO i hx))] using hKO i hx⟩)
  refine ⟨R, hR, ?_⟩
  intro i x hx t ht
  apply hmargin (fun y => e y - t) ?_ i hx
  intro y
  rw [edist_dist, dist_eq_norm]
  have heq : e y - t - e y = -t := by abel
  rw [heq, norm_neg]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr
    (by simpa only [mem_ball, dist_zero_right] using ht)

end PoincareConjecture.M40
