import PoincareConjecture.Proofs.M30.Universe.OutputLiftJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

noncomputable def liftCylinderFromMaps {J : Set ℝ} (L : BlowupLimitFlow.{0} J)
    (F : GeneralizedRicciFlowData.{u}) (origin scale : ℝ) (I : Set ℝ)
    (U : Set L.sliceCarrier.carrier) (hscale : 0 < scale)
    (f : ∀ s : ℝ, s ∈ I →
      L.sliceCarrier.carrier → (F.slice (origin + s / scale)).carrier)
    (g : ∀ s : ℝ, s ∈ I →
      (F.slice (origin + s / scale)).carrier → L.sliceCarrier.carrier)
    (hf : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) U)
    (hg : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (g s hs) (f s hs '' U))
    (hleft : ∀ s hs, LeftInvOn (g s hs) (f s hs) U)
    (hright : ∀ s hs, LeftInvOn (f s hs) (g s hs) (f s hs '' U))
    (hemb : Topology.IsEmbedding (fun p : I × U =>
      (⟨origin + p.1.val / scale, f p.1.val p.1.property p.2.val⟩ : F.point)))
    (hvertical : ∀ s, s ∈ I → ∀ x, x ∈ U →
      ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
        ∀ s' hs', |s' - s| < δ →
          ∃ hb : origin + s' / scale ∈ (F.box b).interval,
            f s' hs' x = (F.box b).forward (origin + s' / scale) hb y) :
    GeneralizedFlowCylinder F (liftBlowupLimit.{u} L).sliceCarrier origin scale I
      ((ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) ⁻¹' U) := by
  let : TopologicalSpace (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.isManifold
  have hd : ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) :=
    (Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.sliceCarrier.carrier).contMDiff
  have hu : ContMDiff (𝓡 3) (𝓡 3) ∞
      (ULift.up : L.sliceCarrier.carrier → ULift.{u} L.sliceCarrier.carrier) :=
    (Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.sliceCarrier.carrier).symm.contMDiff
  refine {
    scale_pos := hscale
    forward := fun s hs x => f s hs x.down
    inverse := fun s hs y => ULift.up (g s hs y)
    forward_smooth := fun s hs => (hf s hs).comp hd.contMDiffOn (fun _ hx => hx)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := ?_
    vertical_compatibility := fun s hs x hx => hvertical s hs x.down hx }
  · intro s hs
    apply hu.comp_contMDiffOn
    apply (hg s hs).mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.down, hx, rfl⟩
  · intro s hs x hx
    change ULift.up (g s hs (f s hs x.down)) = x
    rw [hleft s hs hx]
    exact ULift.up_down x
  · intro s hs y hy
    change f s hs (g s hs y) = y
    apply hright s hs
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x.down, hx, rfl⟩
  · let hsub :
        ((ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) ⁻¹' U)
          ≃ₜ U :=
      (Homeomorph.ulift : ULift.{u} L.sliceCarrier.carrier ≃ₜ L.sliceCarrier.carrier).subtype
        (fun _ => Iff.rfl)
    exact hemb.comp (Topology.IsEmbedding.id.prodMap hsub.isEmbedding)

private noncomputable def mixedPullbackInner
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{0}}
    {origin scale : ℝ} {I : Set ℝ}
    (f : ∀ s : ℝ, s ∈ I → C.carrier → (F.slice (origin + s / scale)).carrier)
    (s : ℝ) (x : C.carrier) (v w : TangentSpace (𝓡 3) x) : ℝ := by
  classical
  exact if hs : s ∈ I then
    scale * (F.metric (origin + s / scale)).inner (f s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (f s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (f s hs) x w)
  else 0

private theorem liftCylinder_coefficient_eq {J : Set ℝ} (L : BlowupLimitFlow.{0} J)
    {F : GeneralizedRicciFlowData.{u}} {origin scale : ℝ} {I : Set ℝ}
    {U : Set L.sliceCarrier.carrier} (hU : IsOpen U)
    (f : ∀ s : ℝ, s ∈ I →
      L.sliceCarrier.carrier → (F.slice (origin + s / scale)).carrier)
    (hf : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) U)
    (e : GeneralizedFlowCylinder F (liftBlowupLimit.{u} L).sliceCarrier origin scale I
      ((ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) ⁻¹' U))
    (hforward : ∀ s hs x, e.forward s hs x = f s hs x.down)
    (q : L.sliceCarrier.carrier) (a b : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ I ×ˢ (extChartAt (𝓡 3) q).target)
    (hx : (extChartAt (𝓡 3) q).symm p.2 ∈ U) :
    blowupPullbackCoefficient e (ULift.up q) a b p =
      L.carrier.coordinateCoefficient q (mixedPullbackInner f) a b p := by
  let : TopologicalSpace (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.isManifold
  let y := (extChartAt (𝓡 3) (ULift.up.{u} q)).symm p.2
  have hy : y.down ∈ U := by
    change (extChartAt (𝓡 3) q).symm p.2 ∈ U
    exact hx
  have hd : MDifferentiable (𝓡 3) (𝓡 3)
      (ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) :=
    (Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.sliceCarrier.carrier).contMDiff.mdifferentiable
      (by simp)
  have hf' := ((hf p.1 hp.1).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hfun : e.forward p.1 hp.1 =
      f p.1 hp.1 ∘ (ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) :=
    funext (hforward p.1 hp.1)
  have hderiv : mfderiv (𝓡 3) (𝓡 3) (e.forward p.1 hp.1) y =
      (mfderiv (𝓡 3) (𝓡 3) (f p.1 hp.1) y.down).comp
        (mfderiv (𝓡 3) (𝓡 3)
          (ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) y) := by
    rw [hfun]
    exact mfderiv_comp y hf' (hd y)
  have hcoef := liftFlowCarrier_coordinateCoefficient_eqOn.{u} L.carrier q
    (mixedPullbackInner f) I a b hp
  apply Eq.trans ?_ hcoef
  dsimp only [blowupPullbackCoefficient]
  rw [dif_pos hp.1]
  dsimp only [GeneralizedFlowCylinder.pullbackInner, FlowCarrier.coordinateCoefficient]
  rw [mixedPullbackInner, dif_pos hp.1, hderiv, hforward]
  rfl

theorem liftCylinder_iteratedFDerivWithin_coefficient
    {J : Set ℝ} (L : BlowupLimitFlow.{0} J)
    {F : GeneralizedRicciFlowData.{u}} {origin scale : ℝ} {I : Set ℝ}
    {U : Set L.sliceCarrier.carrier} (hU : IsOpen U)
    (f : ∀ s : ℝ, s ∈ I →
      L.sliceCarrier.carrier → (F.slice (origin + s / scale)).carrier)
    (hf : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) U)
    (e : GeneralizedFlowCylinder F (liftBlowupLimit.{u} L).sliceCarrier origin scale I
      ((ULift.down : ULift.{u} L.sliceCarrier.carrier → L.sliceCarrier.carrier) ⁻¹' U))
    (hforward : ∀ s hs x, e.forward s hs x = f s hs x.down)
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
    letI : DecidablePred (fun s : ℝ => s ∈ I) := Classical.decPred _
    iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e (ULift.up q) a b)
        (I ×ˢ (extChartAt (𝓡 3) (ULift.up.{u} q)).target) p =
      iteratedFDerivWithin ℝ r
        (L.carrier.coordinateCoefficient q
          (fun s x v w => if hs : s ∈ I then
            scale * (F.metric (origin + s / scale)).inner (f s hs x)
              (mfderiv (𝓡 3) (𝓡 3) (f s hs) x v)
              (mfderiv (𝓡 3) (𝓡 3) (f s hs) x w)
            else 0) a b)
        (I ×ˢ (extChartAt (𝓡 3) q).target) p := by
  let : TopologicalSpace (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ (ULift.{u} L.sliceCarrier.carrier) :=
    (liftBlowupLimit.{u} L).carrier.isManifold
  have htarget : (extChartAt (𝓡 3) (ULift.up.{u} q)).target =
      (extChartAt (𝓡 3) q).target := by
    ext y
    have h := Set.ext_iff.mp (liftBlowupLimit_metricChartDomain.{u} L q) (0, y)
    simpa only [blowupMetricChartDomain, mem_prod, L.zero_mem, true_and] using h
  rw [htarget]
  change iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e (ULift.up q) a b)
      (I ×ˢ (extChartAt (𝓡 3) q).target) p =
    iteratedFDerivWithin ℝ r
      (L.carrier.coordinateCoefficient q (mixedPullbackInner f) a b)
      (I ×ˢ (extChartAt (𝓡 3) q).target) p
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hp.2).contMDiffAt
    (extChartAt_target_mem_nhds' hp.2)
  have hstage : ∀ᶠ z : ℝ × EuclideanSpace ℝ (Fin 3) in 𝓝 p,
      (extChartAt (𝓡 3) q).symm z.2 ∈ U :=
    (hc.continuousAt.comp continuousAt_snd).preimage_mem_nhds (hU.mem_nhds hx)
  have heq : blowupPullbackCoefficient e (ULift.up q) a b
      =ᶠ[𝓝[I ×ˢ (extChartAt (𝓡 3) q).target] p]
        L.carrier.coordinateCoefficient q (mixedPullbackInner f) a b := by
    filter_upwards [hstage.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hDz
    exact liftCylinder_coefficient_eq L hU f hf e hforward q a b z hDz hz
  exact heq.iteratedFDerivWithin_eq
    (liftCylinder_coefficient_eq L hU f hf e hforward q a b p hp hx) r

end PoincareConjecture.M30
