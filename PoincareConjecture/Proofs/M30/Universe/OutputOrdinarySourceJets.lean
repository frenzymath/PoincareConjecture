import PoincareConjecture.Proofs.M30.Universe.OutputSourceLiftJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

private noncomputable def ordinarySourceRawInner
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{0}}
    {Dsrc : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {I : Set ℝ}
    (V : TopologicalSpace.Opens Dsrc.carrier)
    (Esrc : GeneralizedFlowCylinder F Dsrc origin scale I V) (a0 : C.carrier → V)
    (s : ℝ) (x : C.carrier) (v w : TangentSpace (𝓡 3) x) : ℝ := by
  classical
  exact if hs : s ∈ I then
    scale * (F.metric (origin + s / scale)).inner (Esrc.forward s hs (a0 x).val)
      (mfderiv (𝓡 3) (𝓡 3) (fun y => Esrc.forward s hs (a0 y).val) x v)
      (mfderiv (𝓡 3) (𝓡 3) (fun y => Esrc.forward s hs (a0 y).val) x w)
  else 0

private theorem rawCoefficient_eq_ordinary
    {J : Set ℝ} (L : BlowupLimitFlow.{0} J)
    {F : GeneralizedRicciFlowData.{u}} {Dsrc : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (V : TopologicalSpace.Opens Dsrc.carrier)
    (Esrc : GeneralizedFlowCylinder F Dsrc origin scale I V) (G : RicciFlow 3 V I)
    (hmetric : ∀ s (hs : s ∈ I) (z : V) (v w : TangentSpace (𝓡 3) z),
      (G.metric s).inner z v w = Esrc.pullbackInner s hs z.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → Dsrc.carrier) z v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → Dsrc.carrier) z w))
    {U : Set L.sliceCarrier.carrier} (hU : IsOpen U) (a0 : L.sliceCarrier.carrier → V)
    (ha0 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ a0 U)
    (q : L.sliceCarrier.carrier) (a b : Fin 3) (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ I ×ˢ (extChartAt (𝓡 3) q).target)
    (hx : (extChartAt (𝓡 3) q).symm p.2 ∈ U) :
    L.carrier.coordinateCoefficient q (ordinarySourceRawInner V Esrc a0) a b p =
      ((G.metric p.1).pullbackCoefficients (a0 ∘ (extChartAt (𝓡 3) q).symm) p.2)
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  let x := (extChartAt (𝓡 3) q).symm p.2
  let inc : V → Dsrc.carrier := Subtype.val
  let f : L.sliceCarrier.carrier → (F.slice (origin + p.1 / scale)).carrier :=
    fun y => Esrc.forward p.1 hp.1 (a0 y).val
  have ha : ContMDiffAt (𝓡 3) (𝓡 3) ∞ a0 x := ha0.contMDiffAt (hU.mem_nhds hx)
  have hi : ContMDiff (𝓡 3) (𝓡 3) ∞ inc := contMDiff_subtype_val
  have hia : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (inc ∘ a0) x := (hi (a0 x)).comp x ha
  have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Esrc.forward p.1 hp.1) (a0 x).val :=
    (Esrc.forward_smooth p.1 hp.1).contMDiffAt (V.isOpen.mem_nhds (a0 x).property)
  have hdf : mfderiv (𝓡 3) (𝓡 3) f x =
      (mfderiv (𝓡 3) (𝓡 3) (Esrc.forward p.1 hp.1) (a0 x).val).comp
        ((mfderiv (𝓡 3) (𝓡 3) inc (a0 x)).comp (mfderiv (𝓡 3) (𝓡 3) a0 x)) := by
    change mfderiv (𝓡 3) (𝓡 3) (Esrc.forward p.1 hp.1 ∘ (inc ∘ a0)) x = _
    rw [mfderiv_comp x (he.mdifferentiableAt (by simp)) (hia.mdifferentiableAt (by simp)),
      mfderiv_comp x ((hi (a0 x)).mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))]
    rfl
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hp.2).contMDiffAt
    (extChartAt_target_mem_nhds' hp.2)
  have hdc : mfderiv (𝓡 3) (𝓡 3) (a0 ∘ (extChartAt (𝓡 3) q).symm) p.2 =
      (mfderiv (𝓡 3) (𝓡 3) a0 x).comp
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p.2) :=
    mfderiv_comp p.2 (ha.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  dsimp only [FlowCarrier.coordinateCoefficient, ordinarySourceRawInner]
  rw [dif_pos hp.1]
  change scale * (F.metric (origin + p.1 / scale)).inner (Esrc.forward p.1 hp.1 (a0 x).val)
      (mfderiv (𝓡 3) (𝓡 3) f x
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p.2
          (EuclideanSpace.basisFun (Fin 3) ℝ a)))
      (mfderiv (𝓡 3) (𝓡 3) f x
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p.2
          (EuclideanSpace.basisFun (Fin 3) ℝ b))) =
    (G.metric p.1).inner (a0 x)
      (mfderiv (𝓡 3) (𝓡 3) (a0 ∘ (extChartAt (𝓡 3) q).symm) p.2
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) (a0 ∘ (extChartAt (𝓡 3) q).symm) p.2
        (EuclideanSpace.basisFun (Fin 3) ℝ b))
  rw [hdf, hdc, hmetric p.1 hp.1 (a0 x)]
  rfl

theorem liftCylinder_iteratedFDerivWithin_ordinaryCoefficient
    {J : Set ℝ} (L : BlowupLimitFlow.{0} J)
    {F : GeneralizedRicciFlowData.{u}} {Dsrc : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (V : TopologicalSpace.Opens Dsrc.carrier)
    (Esrc : GeneralizedFlowCylinder F Dsrc origin scale I V) (G : RicciFlow 3 V I)
    (hmetric : ∀ s (hs : s ∈ I) (z : V) (v w : TangentSpace (𝓡 3) z),
      (G.metric s).inner z v w = Esrc.pullbackInner s hs z.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → Dsrc.carrier) z v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → Dsrc.carrier) z w))
    {U : Set L.sliceCarrier.carrier} (hU : IsOpen U) (a0 : L.sliceCarrier.carrier → V)
    (ha0 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ a0 U)
    (e : GeneralizedFlowCylinder F (liftBlowupLimit.{u} L).sliceCarrier origin scale I
      ((ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) ⁻¹' U))
    (hforward : ∀ s hs x, e.forward s hs x = Esrc.forward s hs (a0 x.down).val)
    (q : L.sliceCarrier.carrier) (a b : Fin 3) (r : ℕ)
    (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ I ×ˢ (extChartAt (𝓡 3) q).target)
    (hx : (extChartAt (𝓡 3) q).symm p.2 ∈ U) :
    letI : TopologicalSpace (ULift.{u} L.sliceCarrier.carrier) :=
      (liftBlowupLimit.{u} L).carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.sliceCarrier.carrier) :=
      (liftBlowupLimit.{u} L).carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ (ULift.{u} L.sliceCarrier.carrier) :=
      (liftBlowupLimit.{u} L).carrier.isManifold
    iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e (ULift.up q) a b)
        (I ×ˢ (extChartAt (𝓡 3) (ULift.up.{u} q)).target) p =
      iteratedFDerivWithin ℝ r
        (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
          ((G.metric z.1).pullbackCoefficients (a0 ∘ (extChartAt (𝓡 3) q).symm) z.2)
            (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
        (I ×ˢ (extChartAt (𝓡 3) q).target) p := by
  classical
  let : TopologicalSpace (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.isManifold
  let f := fun s (hs : s ∈ I) (x : L.sliceCarrier.carrier) =>
    Esrc.forward s hs (a0 x).val
  have hi : ContMDiff (𝓡 3) (𝓡 3) ∞ (Subtype.val : V → Dsrc.carrier) :=
    contMDiff_subtype_val
  have hf (s : ℝ) (hs : s ∈ I) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) U :=
    (Esrc.forward_smooth s hs).comp (hi.comp_contMDiffOn ha0) (fun x _ => (a0 x).property)
  let Ψ := L.carrier.coordinateCoefficient q (ordinarySourceRawInner V Esrc a0) a b
  let Φ := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    ((G.metric z.1).pullbackCoefficients (a0 ∘ (extChartAt (𝓡 3) q).symm) z.2)
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
  have hraw : iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e (ULift.up q) a b)
        (I ×ˢ (extChartAt (𝓡 3) (ULift.up.{u} q)).target) p =
      iteratedFDerivWithin ℝ r Ψ (I ×ˢ (extChartAt (𝓡 3) q).target) p :=
    liftCylinder_iteratedFDerivWithin_coefficient L hU f hf e hforward q a b r p hp hx
  refine hraw.trans ?_
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hp.2).contMDiffAt
    (extChartAt_target_mem_nhds' hp.2)
  have hstage : ∀ᶠ z : ℝ × EuclideanSpace ℝ (Fin 3) in 𝓝 p,
      (extChartAt (𝓡 3) q).symm z.2 ∈ U :=
    (hc.continuousAt.comp continuousAt_snd).preimage_mem_nhds (hU.mem_nhds hx)
  have heq : Ψ =ᶠ[𝓝[I ×ˢ (extChartAt (𝓡 3) q).target] p] Φ := by
    filter_upwards [hstage.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hDz
    exact rawCoefficient_eq_ordinary L V Esrc G hmetric hU a0 ha0 q a b z hDz hz
  exact heq.iteratedFDerivWithin_eq
    (rawCoefficient_eq_ordinary L V Esrc G hmetric hU a0 ha0 q a b p hp hx) r

end PoincareConjecture.M30
