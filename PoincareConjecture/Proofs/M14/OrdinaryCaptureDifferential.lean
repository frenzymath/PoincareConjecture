import PoincareConjecture.Proofs.M14.OrdinaryCaptureBranches
import PoincareConjecture.Proofs.M14.OrdinaryCaptureSlice
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialSliceInverse

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] {K : SpacetimeInterval}
  {e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C}
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {τmax : ℝ}
  (t₀ : (G.timeIntervals.interval K).Point) (c₀ : C)
  (D : M14OrdinaryCaptureData G C K e g F t₀.val τmax)
  (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)

include D hCoordinates

theorem ordinaryCapture_differential_bijective_iff
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    (A : LExponentialFamily F t₀.val τmax c₀) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hvalid : t₀.val - τ ∈ K.domain) (W : TangentSpace (𝓡 n) c₀)
    (hW : (g.spatialTangentEquiv t₀ c₀ W, Real.sqrt τ) ∈ E.domain)
    (U : Set (TangentSpace (𝓡 n) c₀)) (hU : IsOpen U) (hWU : W ∈ U)
    (hsurv : ∀ V ∈ U, (g.spatialTangentEquiv t₀ c₀ V, Real.sqrt τ) ∈ E.domain)
    (heq : ∀ V ∈ U, E.gamma (g.spatialTangentEquiv t₀ c₀ V) (Real.sqrt τ) =
      e.toSpacetime (⟨t₀.val - τ, hvalid⟩, A.gamma V τ)) :
    Function.Bijective (E.differential (g.spatialTangentEquiv t₀ c₀ W) (Real.sqrt τ) hW) ↔
      Function.Bijective (A.sliceDifferential W τ) := by
  let x := e.toSpacetime (t₀, c₀)
  have : T2Space (G.Horizontal x) := FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨metric⟩
  let ordinaryMetric := (F.metric t₀.val).toRiemannianMetric
  let : NormedAddCommGroup (TangentSpace (𝓡 n) c₀) :=
    (ordinaryMetric.toCore c₀).toNormedAddCommGroupOfTopology
      (ordinaryMetric.continuousAt c₀) (ordinaryMetric.isVonNBounded c₀)
  let : InnerProductSpace ℝ (TangentSpace (𝓡 n) c₀) :=
    .ofCoreOfTopology (ordinaryMetric.toCore c₀)
      (ordinaryMetric.continuousAt c₀) (ordinaryMetric.isVonNBounded c₀)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C → Type _) :=
    ⟨ordinaryMetric⟩
  let L := g.spatialTangentEquiv t₀ c₀
  let t : (G.timeIntervals.interval K).Point := ⟨t₀.val - τ, hvalid⟩
  let f := ordinaryCaptureSliceChart D hCoordinates t
  let q₀ := f (A.gamma W τ)
  let B := exponentialSliceMap E τ hτ.le q₀
  have hB := (exponentialSliceMap_contMDiffAt E hτ.le q₀ hW).mdifferentiableAt (by simp)
  have hA := (Proofs.M09.lExponentialFamily_initialSlice_contMDiffAt A W τ hτ hmax)
    |>.mdifferentiableAt (by simp)
  have hf := (ordinaryCaptureSliceChart_smooth D hCoordinates t).mdifferentiableAt
    (x := A.gamma W τ) (by simp)
  have hlocal : (fun V => B (L V)) =ᶠ[𝓝 W] fun V => f (A.gamma V τ) := by
    filter_upwards [hU.mem_nhds hWU] with V hV
    apply Subtype.ext
    exact (exponentialSliceMap_val E hτ.le q₀ (hsurv V hV)).trans (heq V hV)
  have hd := hlocal.mfderiv_eq (I := 𝓘(ℝ, TangentSpace (𝓡 n) c₀)) (I' := 𝓡 n)
  have hleft := mfderiv_comp W hB L.mdifferentiableAt
  have hright := mfderiv_comp W hf hA
  rw [L.mfderiv_eq] at hleft
  have hcomp : (mfderiv (𝓘(ℝ, G.Horizontal (e.toSpacetime (t₀, c₀)))) (𝓡 n)
      B (L W)).comp L.toContinuousLinearMap =
      (mfderiv (𝓡 n) (𝓡 n) f (A.gamma W τ)).comp (A.sliceDifferential W τ) :=
    hleft.symm.trans (hd.trans hright)
  have hfb : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f (A.gamma W τ)) := by
    let d := (ordinaryCapture_movingCalculus D hCoordinates).slice_localDiffeomorph t
    exact (d.mfderivToContinuousLinearEquiv (by simp) (A.gamma W τ)).bijective
  have hiff := (Function.Bijective.of_comp_iff
    (mfderiv (𝓘(ℝ, G.Horizontal (e.toSpacetime (t₀, c₀)))) (𝓡 n) B (L W)) L.bijective).symm
  have hiff' := Function.Bijective.of_comp_iff' hfb (A.sliceDifferential W τ)
  have hcompare : Function.Bijective
      (mfderiv (𝓘(ℝ, G.Horizontal (e.toSpacetime (t₀, c₀)))) (𝓡 n) B (L W)) ↔
      Function.Bijective (A.sliceDifferential W τ) := by
    rw [hiff]
    change Function.Bijective ((mfderiv
      (𝓘(ℝ, G.Horizontal (e.toSpacetime (t₀, c₀)))) (𝓡 n) B (L W)).comp
      L.toContinuousLinearMap) ↔ _
    rw [hcomp]
    exact hiff'
  exact (exponentialSliceMap_differential_bijective_iff E hτ.le q₀ hW).symm.trans hcompare

end PoincareConjecture.M14
