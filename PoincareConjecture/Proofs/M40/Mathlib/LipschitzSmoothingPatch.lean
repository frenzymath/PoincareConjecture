import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingEstimating
import PoincareConjecture.Proofs.M40.Mathlib.SupportedChartSmoothing
import Mathlib.Topology.UniformSpace.HeineCantor














set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M40

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [LocallyCompactSpace M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
  [MetricSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, F) : N → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : N → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, F) N]





theorem exists_supported_smooth_approximation
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (hes : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target)
    (hhs : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h h.source)
    (hhi : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h.symm h.target)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ)
    (hρrange : ∀ x, ρ x ∈ Icc (0 : ℝ) 1)
    (hρcompact : IsCompact (tsupport ρ)) (hsupp : tsupport ρ ⊆ e.source)
    (f : C(M, N)) (hfsupp : MapsTo f (tsupport ρ) h.source)
    (L : ℝ≥0) (hf : LipschitzWith L f)
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ g : C(M, N),
      (∀ x, ρ =ᶠ[𝓝 x] 1 → ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) ∧
      (∀ x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x →
        ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) ∧
      ContinuousMap.Homotopic g f ∧ (∀ x, dist (g x) (f x) < ε) ∧
      ∀ x, ∃ V ∈ 𝓝 x, LipschitzOnWith (L + ⟨σ, hσ.le⟩) g V := by
  classical
  let U₀ : Set M := e.source ∩ f ⁻¹' h.source
  have hU₀ : IsOpen U₀ := e.open_source.inter (h.open_source.preimage f.continuous)
  have hSU₀ : tsupport ρ ⊆ U₀ := fun x hx => ⟨hsupp hx, hfsupp hx⟩
  let V₀ : Set E := e.target ∩ e.symm ⁻¹' U₀
  have hV₀ : IsOpen V₀ := e.isOpen_inter_preimage_symm hU₀
  have hcoord : ContinuousOn (fun z => h (f (e.symm z))) V₀ := by
    intro z hz
    exact ((h.continuousAt hz.2.2).comp (f := fun z => f (e.symm z))
      (f.continuous.continuousAt.comp (f := e.symm)
        (e.continuousAt_symm hz.1))).continuousWithinAt
  have himage : IsCompact (e '' tsupport ρ) :=
    hρcompact.image_of_continuousOn (e.continuousOn.mono hsupp)
  have hcoordDomain : e '' tsupport ρ ⊆ V₀ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨e.map_source (hsupp hx), ?_⟩
    simpa only [mem_preimage, e.left_inv (hsupp hx)] using hSU₀ hx
  obtain ⟨fext, hfext, hcompact, r, hr, hext⟩ :=
    exists_continuous_compactSupport_extension himage hV₀ hcoordDomain hcoord
  let U : Set M := U₀ ∩ e ⁻¹' thickening r (e '' tsupport ρ)
  have hU : IsOpen U :=
    (e.continuousOn.mono (fun _ hy => hy.1)).isOpen_inter_preimage hU₀
      isOpen_thickening
  have hUe : U ⊆ e.source := fun _ hy => hy.1.1
  have hfU : MapsTo f U h.source := fun _ hy => hy.1.2
  have hSU : tsupport ρ ⊆ U := fun x hx =>
    ⟨hSU₀ hx, self_subset_thickening hr _ ⟨x, hx, rfl⟩⟩
  have hextU (x : M) (hx : x ∈ U) : fext (e x) = h (f x) := by
    rw [hext (thickening_subset_cthickening _ _ hx.2)]
    change h (f (e.symm (e x))) = h (f x)
    rw [e.left_inv (hUe hx)]
  have he : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨hes.mdifferentiableOn (by norm_num), hei.mdifferentiableOn (by norm_num)⟩
  have hh : h.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) :=
    ⟨hhs.mdifferentiableOn (by norm_num), hhi.mdifferentiableOn (by norm_num)⟩
  have hCnear : ∀ᶠ c : ℝ in 𝓝 1,
      c * (c * (L : ℝ) * (c * c)) < (L : ℝ) + σ := by
    have hc : ContinuousAt (fun c : ℝ => c * (c * (L : ℝ) * (c * c))) 1 := by
      fun_prop
    exact hc.eventually_lt continuousAt_const (by simpa using hσ)
  have hCpos : ∀ᶠ c : ℝ in 𝓝[>] 1, 1 < c := self_mem_nhdsWithin
  obtain ⟨c, hc, hcbudget⟩ := (hCpos.and (nhdsWithin_le_nhds hCnear)).exists
  let C : ℝ≥0 := ⟨c, (zero_lt_one.trans hc).le⟩
  have hC : 1 < C := hc
  let L₀ : ℝ≥0 := C * L * (C * C)
  have hCbudget : (C : ℝ) * (L₀ : ℝ) < (L : ℝ) + σ := hcbudget
  obtain ⟨s, B, K, W, D, R, hR, hK, hKU, hcover, hW, hD,
      hWtarget, hbaseRange, hInv, hρLip, htranslated⟩ :=
    exists_finite_chart_smoothing_estimates e h he hh hes hei hhs hhi hf hρ
      hU hUe hfU hρcompact hSU hextU hC
  letI (i : s) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, F) (f i.1.1)) :=
    FiniteDimensional.of_injective (B i).symm.toLinearMap (B i).symm.injective
  letI (i : s) : CompleteSpace (TangentSpace 𝓘(ℝ, F) (f i.1.1)) :=
    FiniteDimensional.complete ℝ _
  have hδnear : ∀ᶠ d : ℝ in 𝓝 0,
      (C : ℝ) * d < ε ∧
        ∀ i : s, (C : ℝ) * ((L₀ : ℝ) + (D i : ℝ) * d) < (L : ℝ) + σ := by
    apply Filter.Eventually.and
    · exact (continuousAt_const.mul continuousAt_id).eventually_lt continuousAt_const
        (by simpa using hε)
    · apply eventually_all.mpr
      intro i
      exact (continuousAt_const.mul
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id))).eventually_lt
          continuousAt_const (by simpa using hCbudget)
  have hδpos : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := self_mem_nhdsWithin
  obtain ⟨d, hd, hdmovement, hdbudget⟩ :=
    (hδpos.and (nhdsWithin_le_nhds hδnear)).exists
  let δ : ℝ≥0 := ⟨d, hd.le⟩
  obtain ⟨φ, hφ, hG, _, hclose, hrange, hLip⟩ :=
    exists_convolution_finite_chart_controls (μ := μ) K hK e
      (fun i => e.continuousOn.mono ((hKU i).trans hUe))
      (hcompact.uniformContinuous_of_continuous hfext) h B W hW hbaseRange
      hρrange (L := fun _ => L₀) (A := D) (δ := fun _ => δ) (C := fun _ => C)
      (fun _ => hd) hρLip hInv hR hε htranslated
  let G := normalizedConvolution μ φ fext
  have hrangeU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : M) (hx : x ∈ U) :
      h (f x) + t • chartSmoothingDisplacement e h ρ f G x ∈ h.target := by
    by_cases hxS : x ∈ tsupport ρ
    · obtain ⟨i, hxi⟩ := hcover x hxS
      have hb := hWtarget i (hrange t ht i (interior_subset hxi))
      have heq : h (f x) + t • chartSmoothingDisplacement e h ρ f G x =
          cutoffBlend (fun y => t * ρ y) (fun y => fext (e y))
            (fun y => G (e y)) x := by
        dsimp [chartSmoothingDisplacement, cutoffBlend]
        rw [hextU x hx]
        module
      rw [heq]
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hb
    · simp only [chartSmoothingDisplacement,
        image_eq_zero_of_notMem_tsupport hxS, zero_smul, smul_zero, add_zero]
      exact h.map_source (hfU hx)
  have hrange₁ (x : M) (hx : x ∈ U) :
      h (f x) + chartSmoothingDisplacement e h ρ f G x ∈ h.target := by
    simpa only [one_smul] using hrangeU 1 ⟨zero_le_one, le_rfl⟩ x hx
  let g : C(M, N) := ⟨supportedChartSmoothing e h U ρ f G,
    continuous_supportedChartSmoothing e h hU hUe hρ.continuous f.continuous
      hG.continuous hSU hfU hrange₁⟩
  have heqOutside (x : M) (hx : x ∉ tsupport ρ) : g x = f x :=
    (supportedChartSmoothing_eventuallyEq e h U ρ f G hfU hx).self_of_nhds
  have heqK (i : s) (x : M) (hx : x ∈ K i) :
      g x = h.symm (cutoffBlend ρ (fun y => fext (e y)) (fun y => G (e y)) x) := by
    rw [show g x = supportedChartSmoothing e h U ρ f G x from rfl,
      supportedChartSmoothing_of_mem e h U ρ f G (hKU i hx)]
    simp only [cutoffBlend, Function.comp_apply, hextU x (hKU i hx)]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact contMDiffAt_supportedChartSmoothing_of_eventuallyEq_one
      e h hU hUe hG hes hhi hSU hrange₁ hx
  · intro x hx
    exact contMDiffAt_supportedChartSmoothing_of_contMDiffAt
      e h hU hUe hρ hG hes hhs hhi hSU hfU hrange₁ hx
  · exact (show ContinuousMap.Homotopic f g from
      ⟨supportedChartSmoothingHomotopy e h hU hUe ρ f G hρ.continuous
        hG.continuous hSU hfU (fun t x hx => hrangeU t t.property x hx)⟩).symm
  · intro x
    by_cases hxS : x ∈ tsupport ρ
    · obtain ⟨i, hxi⟩ := hcover x hxS
      have hxK := interior_subset hxi
      have hb := hrange 1 ⟨zero_le_one, le_rfl⟩ i hxK
      simp only [one_mul] at hb
      have hblend : dist
          (B i (cutoffBlend ρ (fun y => fext (e y)) (fun y => G (e y)) x))
          (B i (fext (e x))) ≤ (δ : ℝ) := by
        simpa only [cutoffBlend, map_add, map_smul] using
          (cutoffBlend_dist_le (ρ := ρ)
            (f := fun y => B i (fext (e y))) (g := fun y => B i (G (e y)))
            (x := x) (hρrange x) (hclose i x hxK).le)
      calc
        dist (g x) (f x) = dist
            (h.symm ((B i).symm
              (B i (cutoffBlend ρ (fun y => fext (e y)) (fun y => G (e y)) x))))
            (h.symm ((B i).symm (B i (fext (e x))))) := by
          rw [(B i).symm_apply_apply, (B i).symm_apply_apply,
            hextU x (hKU i hxK), h.left_inv (hfU (hKU i hxK)), heqK i x hxK]
        _ ≤ (C : ℝ) * dist
            (B i (cutoffBlend ρ (fun y => fext (e y)) (fun y => G (e y)) x))
            (B i (fext (e x))) := (hInv i).dist_le_mul _ hb _ (hbaseRange i hxK)
        _ ≤ (C : ℝ) * δ := mul_le_mul_of_nonneg_left hblend C.coe_nonneg
        _ < ε := hdmovement
    · rw [heqOutside x hxS, dist_self]
      exact hε
  · intro x
    by_cases hxS : x ∈ tsupport ρ
    · obtain ⟨i, hxi⟩ := hcover x hxS
      refine ⟨K i, mem_of_superset (isOpen_interior.mem_nhds hxi) interior_subset, ?_⟩
      have hconstant : C * (L₀ + D i * δ) ≤ L + ⟨σ, hσ.le⟩ := by
        exact_mod_cast (hdbudget i).le
      intro y hy z hz
      rw [heqK i y hy, heqK i z hz]
      exact ((hLip i).weaken hconstant) hy hz
    · refine ⟨(tsupport ρ)ᶜ, (isClosed_tsupport ρ).isOpen_compl.mem_nhds hxS, ?_⟩
      intro y hy z hz
      rw [heqOutside y hy, heqOutside z hz]
      exact (hf.weaken (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ ⟨σ, hσ.le⟩ from
        zero_le))) y z

end PoincareConjecture.M40
