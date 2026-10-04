import PoincareLib.Geometry.RicciFlow.CurveShortening.Connection.Torsion
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Connection
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Commutation
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.SmoothTangentChartPhase
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.CompactFieldExtension

/-!
# Curvature commutation for the actual parameter pullback

The actual frozen derivative has the actual chart Christoffel formula.
The coordinate parameter commutator is therefore the curvature of the
retained connection, with order R(c_t,c_x). This is the interchange used
in MT2015Correction Lemma 0.2, pp. 4-6. See `references/ricci-flow/mapher/curve-evolution/derivations/2026-09-20-pullback-curvature.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareMT.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The actual frozen pullback has the actual chart Christoffel expression;
MT2015Correction Lemma 0.2, pp. 4-6, the parameter commutation calculation. -/
theorem pullback_chart_field_coordinates [T2Space M]
    (D : LeviCivitaData g) (p : M) {gamma : ℝ → M} {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x)
    (hsource : gamma x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {U : Set ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (v : ℝ → EuclideanSpace ℝ (Fin n)) (hv : ContDiffOn ℝ ∞ v U) :
    mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (gamma x)
      (rampHorizontalCovariantDerivative D gamma
        (fun r => PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (v r) (gamma r)) x) =
      deriv v x + RicciFlowAnalysis.shiChartChristoffel D
        (chartAt (EuclideanSpace ℝ (Fin n)) p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (gamma x))
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (gamma x)
          (curveVelocity gamma x)) (v x) := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  rw [pullback_chart_field D p hgamma hsource hU hx v hv, map_add]
  have hfirst : mfderiv (𝓡 n) (𝓡 n) e (gamma x)
      (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (deriv v x) (gamma x)) = deriv v x :=
    RicciFlowAnalysis.shiChartField_duality hc hi hsource (deriv v x)
  rw [hfirst]
  congr 1
  have h := RicciFlowAnalysis.shiChartChristoffel_connection D hc hi (e.map_source hsource)
    (mfderiv (𝓡 n) (𝓡 n) e (gamma x) (curveVelocity gamma x)) (v x)
  rw [← RicciFlowAnalysis.shiChartField_at_inverse hc hi (e.map_source hsource), e.left_inv hsource] at h
  have hcancel : RicciFlowAnalysis.shiChartField e
      (mfderiv (𝓡 n) (𝓡 n) e (gamma x) (curveVelocity gamma x)) (gamma x) =
        curveVelocity gamma x :=
    (RicciFlowAnalysis.shiChart_mfderiv_isInvertible hc hi hsource).inverse_apply_self _
  rw [hcancel] at h
  exact h.symm

/-- The actual parameter pullback commutator is the retained connection's
curvature, in order R(c_t,c_x); MT2015Correction Lemma 0.2, pp. 4-6. -/
theorem pullback_curvature_commute [T2Space M]
    (D : LeviCivitaData g) (c : ℝ → ℝ → M)
    (Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) Omega)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M)) Omega)
    {x t : ℝ} (hxt : (x, t) ∈ Omega) :
    rampHorizontalCovariantDerivative D (fun r => c x r)
      (fun r => rampHorizontalCovariantDerivative D (fun s => c s r)
        (fun s => Y (s, r)) x) t -
    rampHorizontalCovariantDerivative D (fun s => c s t)
      (fun s => rampHorizontalCovariantDerivative D (fun r => c s r)
        (fun r => Y (s, r)) t) x =
      D.curvature (c x t) (curveVelocity (fun r => c x r) t)
        (curveVelocity (fun s => c s t) x) (Y (x, t)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let p := c x t
  let e := chartAt E p
  let U := Omega ∩ (fun z : ℝ × ℝ => c z.1 z.2) ⁻¹' e.source
  have hU : IsOpen U := hc.continuousOn.isOpen_inter_preimage hOmega e.open_source
  have hbase : p ∈ e.source := mem_chart_source E p
  have hz : (x, t) ∈ U := ⟨hxt, hbase⟩
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  let q : ℝ × ℝ → E := fun z => e (c z.1 z.2)
  let W : ℝ × ℝ → E := fun z => mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2) (Y z)
  let Gamma : ℝ × E → E →L[ℝ] E →L[ℝ] E :=
    fun z => RicciFlowAnalysis.shiChartChristoffel D e z.2
  have hq : ContDiffOn ℝ ∞ q U :=
    (he.comp (hc.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  have hW : ContDiffOn ℝ ∞ W U := by
    have h := (PoincareMT.ReducedLengthMinimum.Variation.Geometry.tangentChartPhase_contMDiffOn p).comp
      (hY.mono inter_subset_left) (fun z hz => hz.2)
    exact h.contDiffOn.snd
  have hGamma : ContDiffOn ℝ ∞ Gamma (univ ×ˢ e.target) :=
    (RicciFlowAnalysis.shiChartChristoffel_smooth D he hi).comp contDiffOn_snd (fun z hz => hz.2)
  have hmap : MapsTo (fun z : ℝ × ℝ => (z.1, q z)) U (univ ×ˢ e.target) :=
    fun z hz => ⟨mem_univ _, e.map_source hz.2⟩
  have hcAt (z : ℝ × ℝ) (hz : z ∈ U) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n) (fun z : ℝ × ℝ => c z.1 z.2) z :=
    (hc.contMDiffAt (hOmega.mem_nhds hz.1)).mdifferentiableAt (by simp)
  have hfst (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (r, z.2)) z.1 :=
    (differentiableAt_id.prodMk (differentiableAt_const z.2)).mdifferentiableAt
  have hsnd (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (z.1, r)) z.2 :=
    ((differentiableAt_const z.1).prodMk differentiableAt_id).mdifferentiableAt
  have hX (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS q z) (c z.1 z.2) =
        curveVelocity (fun r => c r z.2) z.1 :=
    PoincareMT.ReducedLength.chartVectorField_coordinate_velocity p (fun r => c r z.2) z.1
      (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS q z) hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.1 (hfst z))
      (ReducedLengthMinimum.Variation.Geometry.coordinateSlice_fst_hasDerivAt q
        ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
  have hT (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (ReducedLengthMinimum.Variation.Geometry.coordinatePartialU q z) (c z.1 z.2) =
        curveVelocity (fun r => c z.1 r) z.2 :=
    PoincareMT.ReducedLength.chartVectorField_coordinate_velocity p (fun r => c z.1 r) z.2
      (ReducedLengthMinimum.Variation.Geometry.coordinatePartialU q z) hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.2 (hsnd z))
      (ReducedLengthMinimum.Variation.Geometry.coordinateSlice_snd_hasDerivAt q
        ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
  have hWvalue (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (W z) (c z.1 z.2) = Y z :=
    PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField_differential p _ _ hz.2
  have hspace (Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
      (V : ℝ × ℝ → E) (hV : ContDiffOn ℝ ∞ V U)
      (hvalue : ∀ z ∈ U, PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (V z) (c z.1 z.2) = Z z)
      (z : ℝ × ℝ) (hz : z ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2)
        (rampHorizontalCovariantDerivative D (fun s => c s z.2)
          (fun s => Z (s, z.2)) z.1) = ReducedLengthMinimum.Variation.Geometry.coordinateCovariantS Gamma q V z := by
    let A := (fun s : ℝ => (s, z.2)) ⁻¹' U
    have hA : IsOpen A := hU.preimage (continuous_id.prodMk continuous_const)
    have hcongr := pullback_congr D (γ := fun s => c s z.2)
      (Y := fun s => Z (s, z.2))
      (Z := fun s => PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (V (s, z.2)) (c s z.2))
      (x := z.1) (by
        filter_upwards [hA.mem_nhds hz] with s hs
        exact (hvalue (s, z.2) hs).symm)
    rw [hcongr, pullback_chart_field_coordinates D p (gamma := fun s => c s z.2) (x := z.1)
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.1 (hfst z))
      hz.2 hA hz (fun s => V (s, z.2))
      (hV.comp (contDiffOn_id.prodMk contDiffOn_const) (fun s hs => hs))]
    rw [(ReducedLengthMinimum.Variation.Geometry.coordinateSlice_fst_hasDerivAt V
      ((hV.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv]
    rw [← hX z hz]
    erw [RicciFlowAnalysis.shiChartField_duality he hi hz.2]
    rfl
  have htime (Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
      (V : ℝ × ℝ → E) (hV : ContDiffOn ℝ ∞ V U)
      (hvalue : ∀ z ∈ U, PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (V z) (c z.1 z.2) = Z z)
      (z : ℝ × ℝ) (hz : z ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2)
        (rampHorizontalCovariantDerivative D (fun r => c z.1 r)
          (fun r => Z (z.1, r)) z.2) = ReducedLengthMinimum.Variation.Geometry.coordinateCovariantU Gamma q V z := by
    let A := (fun r : ℝ => (z.1, r)) ⁻¹' U
    have hA : IsOpen A := hU.preimage (continuous_const.prodMk continuous_id)
    have hcongr := pullback_congr D (γ := fun r => c z.1 r)
      (Y := fun r => Z (z.1, r))
      (Z := fun r => PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (V (z.1, r)) (c z.1 r))
      (x := z.2) (by
        filter_upwards [hA.mem_nhds hz] with r hr
        exact (hvalue (z.1, r) hr).symm)
    rw [hcongr, pullback_chart_field_coordinates D p (gamma := fun r => c z.1 r) (x := z.2)
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.2 (hsnd z))
      hz.2 hA hz (fun r => V (z.1, r))
      (hV.comp (contDiffOn_const.prodMk contDiffOn_id) (fun r hr => hr))]
    rw [(ReducedLengthMinimum.Variation.Geometry.coordinateSlice_snd_hasDerivAt V
      ((hV.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv]
    rw [← hT z hz]
    erw [RicciFlowAnalysis.shiChartField_duality he hi hz.2]
    rfl
  let Yx := fun z : ℝ × ℝ => rampHorizontalCovariantDerivative D
    (fun s => c s z.2) (fun s => Y (s, z.2)) z.1
  let Yt := fun z : ℝ × ℝ => rampHorizontalCovariantDerivative D
    (fun r => c z.1 r) (fun r => Y (z.1, r)) z.2
  have hWx := ReducedLengthMinimum.Variation.Geometry.coordinateCovariantS_contDiffOn hU Gamma q W hGamma hq hW hmap
  have hWt := ReducedLengthMinimum.Variation.Geometry.coordinateCovariantU_contDiffOn hU Gamma q W hGamma hq hW hmap
  have hYx (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p
        (ReducedLengthMinimum.Variation.Geometry.coordinateCovariantS Gamma q W z) (c z.1 z.2) = Yx z := by
    rw [← hspace Y W hW hWvalue z hz]
    exact PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField_differential p _ _ hz.2
  have hYt (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p
        (ReducedLengthMinimum.Variation.Geometry.coordinateCovariantU Gamma q W z) (c z.1 z.2) = Yt z := by
    rw [← htime Y W hW hWvalue z hz]
    exact PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField_differential p _ _ hz.2
  have hGamma0 : DifferentiableAt ℝ (RicciFlowAnalysis.shiChartChristoffel D e) (q (x, t)) :=
    ((RicciFlowAnalysis.shiChartChristoffel_smooth D he hi).contDiffAt
    (e.open_target.mem_nhds (e.map_source hbase))).differentiableAt (by simp)
  have hGammaFull : HasFDerivAt Gamma
      ((fderiv ℝ (RicciFlowAnalysis.shiChartChristoffel D e) (q (x, t))).comp
        (ContinuousLinearMap.snd ℝ ℝ E)) (x, q (x, t)) := by
    change HasFDerivAt ((RicciFlowAnalysis.shiChartChristoffel D e) ∘ (Prod.snd : ℝ × E → E)) _ _
    exact HasFDerivAt.comp (x, q (x, t)) hGamma0.hasFDerivAt
      (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × E → E)
        (ContinuousLinearMap.snd ℝ ℝ E) (x, q (x, t)))
  have hGammaDer (v : ℝ × E) :
      fderiv ℝ Gamma (x, q (x, t)) v =
        fderiv ℝ (RicciFlowAnalysis.shiChartChristoffel D e) (q (x, t)) v.2 := by
    rw [hGammaFull.fderiv]
    rfl
  have hcomm := ReducedLengthMinimum.Variation.Geometry.coordinateCovariant_commutator Gamma q W
    (hq.contDiffAt (hU.mem_nhds hz)) (hW.contDiffAt (hU.mem_nhds hz))
    hGammaFull.differentiableAt
  simp only [hGammaDer, map_zero, zero_apply, sub_zero] at hcomm
  have hR := RicciFlowAnalysis.shiChart_curvature_formula D he hi (e.map_source hbase)
    (ReducedLengthMinimum.Variation.Geometry.coordinatePartialU q (x, t)) (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS q (x, t)) (W (x, t))
  rw [← RicciFlowAnalysis.shiChartField_at_inverse he hi (e.map_source hbase),
    ← RicciFlowAnalysis.shiChartField_at_inverse he hi (e.map_source hbase),
    ← RicciFlowAnalysis.shiChartField_at_inverse he hi (e.map_source hbase), e.left_inv hbase] at hR
  change mfderiv (𝓡 n) (𝓡 n) e p
    (D.curvature p
      (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (ReducedLengthMinimum.Variation.Geometry.coordinatePartialU q (x, t)) p)
      (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (ReducedLengthMinimum.Variation.Geometry.coordinatePartialS q (x, t)) p)
      (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p (W (x, t)) p)) = _ at hR
  rw [hT (x, t) hz, hX (x, t) hz, hWvalue (x, t) hz] at hR
  apply ((mdifferentiable_chart (I := 𝓡 n) p).mfderiv hbase).injective
  change mfderiv (𝓡 n) (𝓡 n) e p (_ - _) = mfderiv (𝓡 n) (𝓡 n) e p _
  rw [map_sub, htime Yx _ hWx hYx (x, t) hz, hspace Yt _ hWt hYt (x, t) hz]
  exact hcomm.trans hR.symm

end PoincareMT.M62
