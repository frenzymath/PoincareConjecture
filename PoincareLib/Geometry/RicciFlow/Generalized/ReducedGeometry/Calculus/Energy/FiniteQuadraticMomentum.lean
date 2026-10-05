import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Energy.FiniteEnergyMomentum
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Coordinates.ClosedChartCoefficients

/-!
# Closed regularity from finite quadratic momentum

The endpoint argument in Morgan-Tian Lemma 6.8, pp. 108-109.
Actual spatial within derivatives are smooth on the closed time
product. Compact coefficient bounds and finite L2 velocity supply the
integrable force required by the finite-energy momentum bootstrap.
-/

set_option autoImplicit false
-- Riesz operators use the same real Hilbert structure as the quadratic forms.
set_option backward.isDefEq.respectTransparency false
-- Spatial derivatives of bilinear forms are triple operator spaces.
set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

private noncomputable local instance dualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private noncomputable local instance trilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance trilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

/-- Positive smooth quadratic coefficients and finite interior L2
velocity give actual closed endpoint regularity from the momentum
equation, the analytic step in Lemma 6.8, pp. 108-109. -/
theorem contDiffOn_of_finite_quadratic_momentum {a b : ℝ} (hab : a < b)
    {S : Set E} (hS : IsOpen S)
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (hB : ContDiffOn ℝ ∞ B (Icc a b ×ˢ S)) (hV : ContDiffOn ℝ ∞ V (Icc a b ×ˢ S))
    (hpos : ∀ z ∈ Icc a b ×ˢ S, ∀ v : E, v ≠ 0 → 0 < B z v v)
    (u d : ℝ → E) (hu : ContinuousOn u (Icc a b)) (hmem : MapsTo u (Icc a b) S)
    (hud : ∀ s ∈ Ioo a b, HasDerivAt u (d s) s)
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hPd : ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => PoincareMT.M08.chartMomentumVector (B (r, u r)) (d r))
        (PoincareMT.M08.chartForceVector
          (PoincareMT.M08.spatialWithinFDeriv (Icc a b) S B (s, u s))
          (PoincareMT.M08.spatialWithinFDeriv (Icc a b) S V (s, u s)) (d s)) s) :
    ContDiffOn ℝ ∞ u (Icc a b) ∧ EqOn (derivWithin u (Icc a b)) d (Ioo a b) ∧
      ∀ s ∈ Icc a b,
        HasDerivWithinAt
          (fun r => PoincareMT.M08.chartMomentumVector (B (r, u r))
            (derivWithin u (Icc a b) r))
          (PoincareMT.M08.chartForceVector
            (PoincareMT.M08.spatialWithinFDeriv (Icc a b) S B (s, u s))
            (PoincareMT.M08.spatialWithinFDeriv (Icc a b) S V (s, u s))
            (derivWithin u (Icc a b) s)) (Icc a b) s := by
  let C := Icc a b
  let DB := PoincareMT.M08.spatialWithinFDeriv C S B
  let DV := PoincareMT.M08.spatialWithinFDeriv C S V
  have hDB : ContDiffOn ℝ ∞ DB (C ×ˢ S) :=
    PoincareMT.M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hS B hB
  have hDV : ContDiffOn ℝ ∞ DV (C ×ˢ S) :=
    PoincareMT.M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hS V hV
  let A := fun z : ℝ × E => InnerProductSpace.continuousLinearMapOfBilin (B z)
  let F := fun t (z : E × E) => PoincareMT.M08.chartForceVector (DB (t, z.1)) (DV (t, z.1)) z.2
  have hA : ContDiffOn ℝ ∞ A (C ×ˢ S) := contDiffOn_const.clm_comp hB
  have hunit : ∀ z ∈ C ×ˢ S, IsUnit (A z) :=
    fun z hz => PoincareMT.M08.positive_form_operator_isUnit (B z) (hpos z hz)
  let Ω := C ×ˢ (S ×ˢ (univ : Set E))
  let k := fun z : ℝ × (E × E) => (z.1, z.2.1)
  have hk : ContDiffOn ℝ ∞ k Ω := contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hkmap : MapsTo k Ω (C ×ˢ S) := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hargs : ContDiffOn ℝ ∞
      (fun z : ℝ × (E × E) => ((DB (z.1, z.2.1), DV (z.1, z.2.1)), z.2.2)) Ω :=
    ((hDB.comp hk hkmap).prodMk (hDV.comp hk hkmap)).prodMk contDiffOn_snd.snd
  have hforce := (PoincareMT.M08.chartForceVector_contDiff (E := E)).comp_contDiffOn hargs
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) Ω := by
    apply hforce.congr
    intro z _
    rfl
  have hgraph : ContinuousOn (fun s => (s, u s)) C := continuousOn_id.prodMk hu
  have hgraphmem : MapsTo (fun s => (s, u s)) C (C ×ˢ S) :=
    fun _ hs => ⟨hs, hmem hs⟩
  have hBc := hB.continuousOn.comp hgraph hgraphmem
  have hDBc := hDB.continuousOn.comp hgraph hgraphmem
  have hDVc := hDV.continuousOn.comp hgraph hgraphmem
  obtain ⟨cB, hcB⟩ := isCompact_Icc.exists_bound_of_continuousOn hBc
  obtain ⟨cDB, hcDB⟩ := isCompact_Icc.exists_bound_of_continuousOn hDBc
  obtain ⟨cDV, hcDV⟩ := isCompact_Icc.exists_bound_of_continuousOn hDVc
  let K := |cB| + |cDB| + |cDV|
  have hK : 0 ≤ K := by positivity
  have hbnd : ∀ s ∈ C, ‖B (s, u s)‖ ≤ K ∧ ‖DB (s, u s)‖ ≤ K ∧ ‖DV (s, u s)‖ ≤ K := by
    intro s hs
    have hb := hcB s hs
    have hdb := hcDB s hs
    have hdv := hcDV s hs
    dsimp only [Function.comp_apply] at hb hdb hdv
    dsimp only [K]
    constructor
    · linarith [le_abs_self cB, abs_nonneg cDB, abs_nonneg cDV]
    constructor
    · linarith [le_abs_self cDB, abs_nonneg cB, abs_nonneg cDV]
    · linarith [le_abs_self cDV, abs_nonneg cB, abs_nonneg cDB]
  have hQ := (PoincareMT.M08.chart_momentum_force_intervalIntegrable hab.le hK d hd
    (fun s => B (s, u s)) (fun s => DB (s, u s)) (fun s => DV (s, u s))
    hBc hDBc hDVc hbnd).2
  exact contDiffOn_of_finite_energy_momentum hab A F hA hunit hF u d hu hmem hud hd hQ hPd

end ODE
