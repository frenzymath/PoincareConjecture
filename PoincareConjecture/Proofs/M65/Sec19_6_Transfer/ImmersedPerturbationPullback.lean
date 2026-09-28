import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem angular_slice_hasDerivAt (f : P × (ℝ × ℝ) → E) (z : P × (ℝ × ℝ))
    (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun x => f (z.1, (x, z.2.2)))
      (fderiv ℝ f z (0, (1, 0))) z.2.1 := by
  have hline : HasDerivAt (fun x : ℝ => (z.1, (x, z.2.2))) (0, (1, 0)) z.2.1 :=
    (hasDerivAt_const z.2.1 z.1).prodMk
      ((hasDerivAt_id z.2.1).prodMk (hasDerivAt_const z.2.1 z.2.2))
  simpa only [Function.comp_def, Prod.eta] using
    hf.hasFDerivAt.comp_hasDerivAt z.2.1 hline

theorem angular_partial_contDiffOn (f : P × (ℝ × ℝ) → E)
    (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z (0, (1, 0))) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] {a b : ℝ}

theorem pullback_angular_contMDiffOn (F : RicciFlow 3 M (Icc a b))
    (c : P × (ℝ × ℝ) → M) (U : Set (P × (ℝ × ℝ))) (hU : IsOpen U)
    (hTime : ∀ z ∈ U, z.2.2 ∈ Icc a b)
    (hc : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞ c U)
    (Y : (z : P × (ℝ × ℝ)) → TangentSpace (𝓡 3) (c z))
    (hY : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z, Y z⟩ : TangentBundle (𝓡 3) M)) U) :
    ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z,
        rampHorizontalCovariantDerivative (F.connection z.2.2)
          (fun x => c (z.1, (x, z.2.2))) (fun x => Y (z.1, (x, z.2.2))) z.2.1⟩ :
            TangentBundle (𝓡 3) M)) U := by
  intro z0 hz0
  let : NormedAddCommGroup (LoopAmbient →L[ℝ] LoopAmbient) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (LoopAmbient →L[ℝ] LoopAmbient) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] LoopAmbient) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] LoopAmbient) :=
    ContinuousLinearMap.toNormedSpace
  let p := c z0
  let e := chartAt LoopAmbient p
  let V := U ∩ c ⁻¹' e.source
  have hV : IsOpen V := hc.continuousOn.isOpen_inter_preimage hU e.open_source
  have hzV : z0 ∈ V := ⟨hz0, mem_chart_source LoopAmbient p⟩
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := contMDiffOn_chart_symm
  let q : P × (ℝ × ℝ) → LoopAmbient := fun z => e (c z)
  let W : P × (ℝ × ℝ) → LoopAmbient :=
    fun z => mfderiv (𝓡 3) (𝓡 3) e (c z) (Y z)
  let G : ℝ × LoopAmbient → LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] LoopAmbient :=
    fun z => M04.shiChartChristoffel (F.connection z.1) e z.2
  let B : P × (ℝ × ℝ) → LoopAmbient := fun z =>
    fderiv ℝ W z (0, (1, 0)) +
      G (z.2.2, q z) (fderiv ℝ q z (0, (1, 0))) (W z)
  let A := fun z : P × (ℝ × ℝ) => rampHorizontalCovariantDerivative
    (F.connection z.2.2) (fun x => c (z.1, (x, z.2.2)))
      (fun x => Y (z.1, (x, z.2.2))) z.2.1
  have hq : ContDiffOn ℝ ∞ q V :=
    (he.comp (hc.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  have hW : ContDiffOn ℝ ∞ W V := by
    have h := (Proofs.M09.tangentChartPhase_contMDiffOn p).comp
      (hY.mono inter_subset_left) (fun z hz => hz.2)
    exact h.contDiffOn.snd
  have hG : ContDiffOn ℝ ∞ G (Icc a b ×ˢ e.target) :=
    M62.flow_chartChristoffel_smooth F p
  have hcoeff : ContDiffOn ℝ ∞ (fun z : P × (ℝ × ℝ) => G (z.2.2, q z)) V :=
    hG.comp (contDiffOn_snd.snd.prodMk hq)
      (fun z hz => ⟨hTime z hz.1, e.map_source hz.2⟩)
  have hB : ContDiffOn ℝ ∞ B V :=
    (angular_partial_contDiffOn W V hV hW).add
      ((hcoeff.clm_apply (angular_partial_contDiffOn q V hV hq)).clm_apply hW)
  have hcoords (z : P × (ℝ × ℝ)) (hz : z ∈ V) :
      mfderiv (𝓡 3) (𝓡 3) e (c z) (A z) = B z := by
    have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, P × (ℝ × ℝ))
        (fun x : ℝ => (z.1, (x, z.2.2))) z.2.1 :=
      ((differentiableAt_const z.1).prodMk
        (differentiableAt_id.prodMk (differentiableAt_const z.2.2))).mdifferentiableAt
    have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3)
        (fun x => c (z.1, (x, z.2.2))) z.2.1 := by
      simpa only [Function.comp_def, Prod.eta] using
        ((hc.contMDiffAt (hU.mem_nhds hz.1)).mdifferentiableAt (by simp)).comp z.2.1 hslice
    let S := (fun x : ℝ => (z.1, (x, z.2.2))) ⁻¹' V
    have hS : IsOpen S := hV.preimage
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))
    have hcongr := M62.pullback_congr (F.connection z.2.2)
      (γ := fun x => c (z.1, (x, z.2.2))) (Y := fun x => Y (z.1, (x, z.2.2)))
      (Z := fun x => Proofs.M09.chartVectorField p (W (z.1, (x, z.2.2)))
        (c (z.1, (x, z.2.2)))) (x := z.2.1) (by
        filter_upwards [hS.mem_nhds hz] with x hx
        exact (Proofs.M09.chartVectorField_differential p _ _ hx.2).symm)
    change mfderiv (𝓡 3) (𝓡 3) e (c z)
      (rampHorizontalCovariantDerivative (F.connection z.2.2)
        (fun x => c (z.1, (x, z.2.2))) (fun x => Y (z.1, (x, z.2.2))) z.2.1) = _
    rw [hcongr, M62.pullback_chart_field_coordinates (F.connection z.2.2) p
      (gamma := fun x => c (z.1, (x, z.2.2))) (x := z.2.1) hcurve hz.2 hS hz
      (fun x => W (z.1, (x, z.2.2)))
      (hW.comp (contDiffOn_const.prodMk (contDiffOn_id.prodMk contDiffOn_const))
        (fun x hx => hx))]
    rw [(angular_slice_hasDerivAt W z
      ((hW.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))).deriv]
    have hvelocity := Proofs.M09.chartVectorField_coordinate_velocity p
      (fun x => c (z.1, (x, z.2.2))) z.2.1 (fderiv ℝ q z (0, (1, 0))) hz.2 hcurve
      (angular_slice_hasDerivAt q z
        ((hq.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)))
    rw [← hvelocity]
    erw [M04.shiChartField_duality he hi hz.2]
  have hphase := (Proofs.M09.inverseTangentChartPhase_contMDiffOn p).comp
    (hq.prodMk hB).contMDiffOn (fun z hz => ⟨e.map_source hz.2, mem_univ _⟩)
  have hactual : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3).tangent ∞
      (fun z => (⟨c z, A z⟩ : TangentBundle (𝓡 3) M)) V := by
    apply hphase.congr
    intro z hz
    change (⟨c z, A z⟩ : TangentBundle (𝓡 3) M) =
      Proofs.M09.inverseTangentChartPhase p (q z, B z)
    rw [← hcoords z hz]
    exact (Proofs.M09.tangentChartPhase_inverse p
      (⟨c z, A z⟩ : TangentBundle (𝓡 3) M) hz.2).symm
  exact (hactual.contMDiffAt (hV.mem_nhds hzV)).contMDiffWithinAt

end PoincareConjecture.M65Perturbation
