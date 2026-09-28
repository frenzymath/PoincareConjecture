import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRegularity

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m63FixedPullback_time_joint_contMDiff [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (c : ℝ → ℝ → M)
    (Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) Omega)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M)) Omega) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ => (⟨c z.1 z.2,
        rampHorizontalCovariantDerivative D (fun r => c z.1 r)
          (fun r => Y (z.1, r)) z.2⟩ : TangentBundle (𝓡 n) M)) Omega := by
  intro z0 hz0
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let p := c z0.1 z0.2
  let e := chartAt E p
  let U := Omega ∩ (fun z : ℝ × ℝ => c z.1 z.2) ⁻¹' e.source
  have hU : IsOpen U := hc.continuousOn.isOpen_inter_preimage hOmega e.open_source
  have hbase : p ∈ e.source := mem_chart_source E p
  have hzU : z0 ∈ U := ⟨hz0, hbase⟩
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  let q : ℝ × ℝ → E := fun z => e (c z.1 z.2)
  let W : ℝ × ℝ → E := fun z => mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2) (Y z)
  let Gamma : E → E →L[ℝ] E →L[ℝ] E := M04.shiChartChristoffel D e
  let V : ℝ × ℝ → E := fun z => M08.coordinatePartialU W z +
    Gamma (q z) (M08.coordinatePartialU q z) (W z)
  let A := fun z : ℝ × ℝ => rampHorizontalCovariantDerivative D
    (fun r => c z.1 r) (fun r => Y (z.1, r)) z.2
  have hq : ContDiffOn ℝ ∞ q U :=
    (he.comp (hc.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  have hW : ContDiffOn ℝ ∞ W U := by
    have h := (Proofs.M09.tangentChartPhase_contMDiffOn p).comp
      (hY.mono inter_subset_left) (fun z hz => hz.2)
    exact h.contDiffOn.snd
  have hGamma : ContDiffOn ℝ ∞ Gamma e.target := M04.shiChartChristoffel_smooth D he hi
  have hcoeff : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Gamma (q z)) U :=
    hGamma.comp hq (fun z hz => e.map_source hz.2)
  have hV : ContDiffOn ℝ ∞ V U :=
    (M08.coordinatePartialU_contDiffOn hU W hW).add
      ((hcoeff.clm_apply (M08.coordinatePartialU_contDiffOn hU q hq)).clm_apply hW)
  have hcoords (z : ℝ × ℝ) (hz : z ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2) (A z) = V z := by
    have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun r : ℝ => (z.1, r)) z.2 :=
      ((differentiableAt_const z.1).prodMk differentiableAt_id).mdifferentiableAt
    have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => c z.1 r) z.2 := by
      simpa only [Function.comp_def] using
        ((hc.contMDiffAt (hOmega.mem_nhds hz.1)).mdifferentiableAt (by simp)).comp z.2 hslice
    let B := (fun r : ℝ => (z.1, r)) ⁻¹' U
    have hB : IsOpen B := hU.preimage (continuous_const.prodMk continuous_id)
    have hcongr := pullback_congr D (γ := fun r => c z.1 r)
      (Y := fun r => Y (z.1, r))
      (Z := fun r => Proofs.M09.chartVectorField p (W (z.1, r)) (c z.1 r))
      (x := z.2) (by
        filter_upwards [hB.mem_nhds hz] with r hr
        exact (Proofs.M09.chartVectorField_differential p _ _ hr.2).symm)
    change mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2)
      (rampHorizontalCovariantDerivative D (fun r => c z.1 r)
        (fun r => Y (z.1, r)) z.2) = _
    rw [hcongr, pullback_chart_field_coordinates D p
      (gamma := fun r => c z.1 r) (x := z.2) hcurve hz.2 hB hz
      (fun r => W (z.1, r))
      (hW.comp (contDiffOn_const.prodMk contDiffOn_id) (fun r hr => hr))]
    rw [(M08.coordinateSlice_snd_hasDerivAt W
      ((hW.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv]
    have hvelocity := Proofs.M09.chartVectorField_coordinate_velocity p
      (fun r => c z.1 r) z.2 (M08.coordinatePartialU q z) hz.2 hcurve
      (M08.coordinateSlice_snd_hasDerivAt q
        ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
    rw [← hvelocity]
    erw [M04.shiChartField_duality he hi hz.2]
    rfl
  have hphase := (Proofs.M09.inverseTangentChartPhase_contMDiffOn p).comp
    (hq.prodMk hV).contMDiffOn (fun z hz => ⟨e.map_source hz.2, mem_univ _⟩)
  have hactual : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, A z⟩ : TangentBundle (𝓡 n) M)) U := by
    apply hphase.congr
    intro z hz
    change (⟨c z.1 z.2, A z⟩ : TangentBundle (𝓡 n) M) =
      Proofs.M09.inverseTangentChartPhase p (q z, V z)
    rw [← hcoords z hz]
    exact (Proofs.M09.tangentChartPhase_inverse p
      (⟨c z.1 z.2, A z⟩ : TangentBundle (𝓡 n) M) hz.2).symm
  exact (hactual.contMDiffAt (hU.mem_nhds hzU)).contMDiffWithinAt

end PoincareConjecture
