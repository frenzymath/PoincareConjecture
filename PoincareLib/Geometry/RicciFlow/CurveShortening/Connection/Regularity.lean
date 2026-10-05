import PoincareLib.Geometry.RicciFlow.CurveShortening.Connection.Variation
import PoincareLib.Geometry.RicciFlow.CurveShortening.Connection.TangentPhaseZero

/-!
# Regularity of the moving spatial pullback

The actual pullback is additive on differentiable fields, and its spatial
derivative along a smooth parameter family is a smooth actual bundled
field. These justify iterated differentiation in MT2015Correction
Lemma 0.2, pp. 4-6. See `references/ricci-flow/mapher/curve-evolution/derivations/2026-09-20-moving-pullback.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareMT.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- Additivity retains both genuine differentiability premises for the
frozen pullback; MT2015Correction Lemma 0.2, pp. 4-6. -/
theorem pullback_add {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {gamma : ℝ → M}
    {Y Z : (r : ℝ) → TangentSpace (𝓡 n) (gamma r)} {x : ℝ}
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun r => (⟨gamma r, Y r⟩ : TangentBundle (𝓡 n) M)) x)
    (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun r => (⟨gamma r, Z r⟩ : TangentBundle (𝓡 n) M)) x) :
    rampHorizontalCovariantDerivative D gamma (fun r => Y r + Z r) x =
      rampHorizontalCovariantDerivative D gamma Y x +
        rampHorizontalCovariantDerivative D gamma Z x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (gamma x)
  let y : ℝ → EuclideanSpace ℝ (Fin n) := fun r => (e ⟨gamma r, Y r⟩).2
  let z : ℝ → EuclideanSpace ℝ (Fin n) := fun r => (e ⟨gamma r, Z r⟩).2
  rw [mdifferentiableAt_totalSpace] at hY hZ
  have hy : DifferentiableAt ℝ y x := hY.2.differentiableAt
  have hz : DifferentiableAt ℝ z x := hZ.2.differentiableAt
  have hnear : ∀ᶠ r in 𝓝 x, gamma r ∈ e.baseSet :=
    hY.1.continuousAt (e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (gamma x)))
  have heq : (fun r => (e ⟨gamma r, Y r + Z r⟩).2) =ᶠ[𝓝 x] (fun r => y r + z r) := by
    filter_upwards [hnear] with r hr
    change (e ⟨gamma r, Y r + Z r⟩).2 = (e ⟨gamma r, Y r⟩).2 + (e ⟨gamma r, Z r⟩).2
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hr,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hr,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hr, map_add]
  let A := PoincareMT.ReducedLengthMinimum.Variation.Geometry.frozenConnectionEndomorphism D (gamma x)
    (curveVelocity gamma x)
  change e.symmL ℝ (gamma x) (deriv (fun r => (e ⟨gamma r, Y r + Z r⟩).2) x) +
      A (Y x + Z x) =
    (e.symmL ℝ (gamma x) (deriv y x) + A (Y x)) +
      (e.symmL ℝ (gamma x) (deriv z x) + A (Z x))
  rw [heq.deriv_eq, deriv_fun_add hy hz, map_add, map_add]
  abel

/-- The actual moving spatial pullback is a smooth bundled field on the
open parameter domain; MT2015Correction Lemma 0.2, pp. 4-6. -/
theorem flow_pullback_space_smooth [T2Space M]
    (F : RicciFlow n M J) (c : ℝ → ℝ → M)
    (Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega)
    (hTime : ∀ z ∈ Omega, z.2 ∈ interior J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) Omega)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M)) Omega) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ => (⟨c z.1 z.2,
        rampHorizontalCovariantDerivative (F.connection z.2) (fun s => c s z.2)
          (fun s => Y (s, z.2)) z.1⟩ : TangentBundle (𝓡 n) M)) Omega := by
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
  let Gamma : ℝ × E → E →L[ℝ] E →L[ℝ] E :=
    fun z => RicciFlowAnalysis.shiChartChristoffel (F.connection z.1) e z.2
  let V : ℝ × ℝ → E := fun z => ReducedLengthMinimum.Variation.Geometry.coordinatePartialS W z +
    Gamma (z.2, q z) (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS q z) (W z)
  let A := fun z : ℝ × ℝ => rampHorizontalCovariantDerivative (F.connection z.2)
    (fun s => c s z.2) (fun s => Y (s, z.2)) z.1
  have hq : ContDiffOn ℝ ∞ q U :=
    (he.comp (hc.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  have hW : ContDiffOn ℝ ∞ W U := by
    have h := (PoincareMT.ReducedLengthMinimum.Variation.Geometry.tangentChartPhase_contMDiffOn p).comp
      (hY.mono inter_subset_left) (fun z hz => hz.2)
    exact h.contDiffOn.snd
  have hGamma : ContDiffOn ℝ ∞ Gamma (J ×ˢ e.target) := flow_chartChristoffel_smooth F p
  have hcoeff : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Gamma (z.2, q z)) U :=
    hGamma.comp (contDiffOn_snd.prodMk hq)
      (fun z hz => ⟨interior_subset (hTime z hz.1), e.map_source hz.2⟩)
  have hV : ContDiffOn ℝ ∞ V U :=
    (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS_contDiffOn hU W hW).add
      ((hcoeff.clm_apply (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS_contDiffOn hU q hq)).clm_apply hW)
  have hcoords (z : ℝ × ℝ) (hz : z ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2) (A z) = V z := by
    have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun s : ℝ => (s, z.2)) z.1 :=
      (differentiableAt_id.prodMk (differentiableAt_const z.2)).mdifferentiableAt
    have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => c s z.2) z.1 := by
      simpa only [Function.comp_def] using
        ((hc.contMDiffAt (hOmega.mem_nhds hz.1)).mdifferentiableAt (by simp)).comp z.1 hslice
    let B := (fun s : ℝ => (s, z.2)) ⁻¹' U
    have hB : IsOpen B := hU.preimage (continuous_id.prodMk continuous_const)
    have hcongr := pullback_congr (F.connection z.2) (γ := fun s => c s z.2)
      (Y := fun s => Y (s, z.2))
      (Z := fun s => PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (W (s, z.2)) (c s z.2))
      (x := z.1) (by
        filter_upwards [hB.mem_nhds hz] with s hs
        exact (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField_differential p _ _ hs.2).symm)
    change mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2)
      (rampHorizontalCovariantDerivative (F.connection z.2) (fun s => c s z.2)
        (fun s => Y (s, z.2)) z.1) = _
    rw [hcongr, pullback_chart_field_coordinates (F.connection z.2) p
      (gamma := fun s => c s z.2) (x := z.1) hcurve hz.2 hB hz
      (fun s => W (s, z.2))
      (hW.comp (contDiffOn_id.prodMk contDiffOn_const) (fun s hs => hs))]
    rw [(ReducedLengthMinimum.Variation.Geometry.coordinateSlice_fst_hasDerivAt W
      ((hW.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv]
    have hvelocity := PoincareMT.ReducedLength.chartVectorField_coordinate_velocity p
      (fun s => c s z.2) z.1 (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS q z) hz.2 hcurve
      (ReducedLengthMinimum.Variation.Geometry.coordinateSlice_fst_hasDerivAt q
        ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
    rw [← hvelocity]
    erw [RicciFlowAnalysis.shiChartField_duality he hi hz.2]
    rfl
  have hphase := (PoincareMT.ReducedLengthMinimum.Variation.Geometry.inverseTangentChartPhase_contMDiffOn p).comp
    (hq.prodMk hV).contMDiffOn (fun z hz => ⟨e.map_source hz.2, mem_univ _⟩)
  have hactual : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, A z⟩ : TangentBundle (𝓡 n) M)) U := by
    apply hphase.congr
    intro z hz
    change (⟨c z.1 z.2, A z⟩ : TangentBundle (𝓡 n) M) =
      PoincareMT.ReducedLengthMinimum.Variation.Geometry.inverseTangentChartPhase p (q z, V z)
    rw [← hcoords z hz]
    exact (PoincareMT.ReducedLengthMinimum.Variation.Geometry.tangentChartPhase_inverse p
      (⟨c z.1 z.2, A z⟩ : TangentBundle (𝓡 n) M) hz.2).symm
  exact (hactual.contMDiffAt (hU.mem_nhds hzU)).contMDiffWithinAt

end PoincareMT.M62
