import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalRoundCoefficientJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Compactness.CompactSmoothPullback

/-!
# Actual round coefficients in a fixed reference parametrization

The original included M30 coefficients are pulled back through the same
reference map in both slots. Their compact smooth limit is the literal
old normalized comparison tensor. MT Proposition 17.1, pp. 407-408;
limit-canonical-round-jet-transfer.md, B-C.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E3 →L[ℝ] E3 →L[ℝ] ℝ

noncomputable local instance roundParameterDualGroup : NormedAddCommGroup (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance roundParameterDualSpace : NormedSpace ℝ (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance roundParameterBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance roundParameterBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

/-- The actual reconstructed source metric in the fixed reference
parametrization, with the original round normalization. MT Definition
2.16 and Proposition 17.1, pp. 407-408. -/
noncomputable def limitCanonicalRoundParameterField
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {H : GeneralizedRicciFlowData.{u}}
    {origin Q : ℝ} {I : Set ℝ} {W : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder H L.sliceCarrier origin Q I W)
    (q : L.sliceCarrier.carrier) (t c : ℝ) (phi : E3 → L.sliceCarrier.carrier)
    (x : E3) : Bilin :=
  c • (M34.blowupCoordinateBilinear e q t ((extChartAt (𝓡 3) q) (phi x))).bilinearComp
    (fderiv ℝ ((extChartAt (𝓡 3) q) ∘ phi) x)
    (fderiv ℝ ((extChartAt (𝓡 3) q) ∘ phi) x)

/-- Both reference-coordinate slots retain the actual included cylinder
tensor. No change of source map or time is involved. MT Proposition 17.1,
pp. 407-408. -/
theorem limitCanonical_round_parameter_readout
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {H : GeneralizedRicciFlowData.{u}}
    {origin Q : ℝ} {I : Set ℝ} {W : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder H L.sliceCarrier origin Q I W)
    (q : L.sliceCarrier.carrier) (t c : ℝ) (ht : t ∈ I)
    {phi : E3 → L.sliceCarrier.carrier} {x : E3}
    (hphi : MDifferentiableAt (𝓡 3) (𝓡 3) phi x)
    (hq : phi x ∈ (extChartAt (𝓡 3) q).source) (v w : E3) :
    limitCanonicalRoundParameterField e q t c phi x v w =
      c * e.pullbackInner t ht (phi x)
        (mfderiv (𝓡 3) (𝓡 3) phi x v) (mfderiv (𝓡 3) (𝓡 3) phi x w) := by
  exact congrArg (c * ·) (M34.blowupCoordinateBilinear_pullback_apply e q ht hphi hq v w)

section Convergence

variable (P : M47Predecessors.{u}) {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E3 G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

include P

/-- Compact convergence of the actual M30 metric survives the fixed
reference-coordinate pullback and original scalar normalization. Its
limit is the old pulled-back metric, not the reference comparison model.
MT Proposition 17.1, pp. 407-408. -/
theorem limitCanonical_round_parameter_convergence
    (q : G.limit.sliceCarrier.carrier) (t c : ℝ) (ht : t ∈ J)
    {phi : E3 → G.limit.sliceCarrier.carrier} {U : Set E3} (hU : IsOpen U)
    (hphi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ phi U)
    (hq : MapsTo phi U (extChartAt (𝓡 3) q).source) :
    CompactSmoothConvergenceOn
      (fun k => limitCanonicalRoundParameterField (G.embedding k) q t c phi)
      (fun x => c • (G.limit.flow.metric t).pullbackCoefficients phi x) atTop U := by
  let a := (extChartAt (𝓡 3) q) ∘ phi
  have hq' : MapsTo phi U (chartAt E3 q).source := by
    simpa only [extChartAt_source] using hq
  have ha : ContDiffOn ℝ ∞ a U :=
    contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_extChartAt (x := q)).comp hphi hq')
  have haU : MapsTo a U (extChartAt (𝓡 3) q).target :=
    fun x hx => (extChartAt (𝓡 3) q).map_source (hq hx)
  have hb := limitCanonical_round_bilinear_coefficient_convergence P G q t ht
  have hp := hb.pullback_bilinear
    (CompactSmoothConvergenceOn.constant hU ha) haU
  have hmul : ContDiff ℝ ∞ (fun B : Bilin => c • B) :=
    (ContinuousLinearMap.lsmul ℝ ℝ (E := Bilin) c).contDiff
  have hscaled := hp.comp_smooth isOpen_univ hmul.contDiffOn (fun _ _ => mem_univ _)
  apply hscaled.congr (fun _ _ _ => rfl)
  intro x hx
  dsimp only [Function.comp_def]
  congr 1
  ext v w
  have hphi' := ((hphi x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hmodel : (G.limit.flow.metric t).pullbackCoefficients
      (extChartAt (𝓡 3) q).symm (a x) = M34.limitCoordinateBilinear G.limit q t (a x) := by
    ext u v
    exact (M34.limitCoordinateBilinear_apply (L := G.limit) q t (a x) u v).symm
  rw [hmodel]
  exact (M34.limitCoordinateBilinear_pullback_apply (L := G.limit) q t
    hphi' (hq hx) v w).symm

end Convergence

end PoincareMT.M47
