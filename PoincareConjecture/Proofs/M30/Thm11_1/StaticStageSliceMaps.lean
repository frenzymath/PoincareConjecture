import PoincareConjecture.Proofs.M30.Thm11_1.StaticStageSourceFlows
import PoincareConjecture.Proofs.M30.Generalized.CylinderSpatialHomeomorph
import PoincareConjecture.Proofs.M30.Generalized.PullbackCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.PartialCharts











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space




theorem exists_static_stage_slice_partialDiffeomorph
    (S : GeneralizedBlowupSequence.{u})
    (G : PartialPointedMetricConvergence (terminalComponentMetric S)
      (terminalComponentBase S) 1)
    (j N k : ℕ) (hjk : j ≤ k + N) {W T B : ℝ} (hT : 0 < T)
    (E : ControlledBlowupCylinder S (G.subsequence (k + N)) W T B 1) :
    let Y : TopologicalSpace.Opens G.limitCarrier.carrier :=
      ⟨G.exhaustion j, G.exhaustion_open j⟩
    let b := fun x : G.limitCarrier.carrier => (G.embedding (k + N) x).val
    ∀ (P : RicciFlow 3 Y (Icc (-T) 0)),
      (∀ x : Y, b x.val ∈ S.baseBall (G.subsequence (k + N)) W) →
      (∀ s (hs : s ∈ Icc (-T) 0) (x : Y) (v w : TangentSpace (𝓡 3) x),
        (P.metric s).inner x v w = E.embedding.pullbackInner s hs (b x.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => b y.val) x v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => b y.val) x w)) →
      ∀ s (hs : s ∈ Icc (-T) 0),
        let q := S.scale (G.subsequence (k + N))
        let t := (S.base (G.subsequence (k + N))).1 + s / q
        let X := ((S.flow (G.subsequence (k + N))).slice t).carrier
        let h := M13.scaleSmoothMetric
          ((S.flow (G.subsequence (k + N))).metric t) q
          (S.base_scalar_pos (G.subsequence (k + N)))
        let f := fun x : G.limitCarrier.carrier => E.embedding.forward s hs (b x)
        ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limitCarrier.carrier X ∞,
          e.source = G.exhaustion j ∧
          (e : G.limitCarrier.carrier → X) = f ∧
          e.target = f '' G.exhaustion j ∧
          (∀ (x : Y) (v w : TangentSpace (𝓡 3) x),
            (P.metric s).inner x v w = h.inner (e x.val)
              (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => e y.val) x v)
              (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => e y.val) x w)) ∧
          ∀ x : Y, (P.connection s).scalarCurvature x =
            (S.flow (G.subsequence (k + N))).scalar
              (E.embedding.pointMap s hs (b x.val)) / q := by
  classical
  intro Y b P himage hP s hs q t X h f
  let C := (S.flow (G.subsequence (k + N))).slice (S.base (G.subsequence (k + N))).1
  let J : SpacetimeInterval := {
    domain := Icc (-T) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩,
      by linarith⟩ }
  let U : TopologicalSpace.Opens C.carrier :=
    ⟨S.baseBall (G.subsequence (k + N)) W,
      baseBall_isOpen S (G.subsequence (k + N)) W⟩
  have hb : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ b (G.exhaustion j) := by
    intro x
    exact (G.embedding_smooth (k + N)
      ⟨x.val, G.exhaustion_monotone hjk x.property⟩).comp (𝓡 3) C.carrier
        (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3)
          (Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3))
            (S.base (G.subsequence (k + N))).2) (G.embedding (k + N) x.val))
  have hbY : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : Y => b y.val) := by
    intro x
    exact ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y x).comp
      (𝓡 3) C.carrier (hb ⟨x.val, x.property⟩)).contMDiffAt
  let c := Cylinder.spatialHomeomorph (J := J) (U := U) E.embedding ⟨s, hs⟩
  let cD : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier X ∞ := {
    toPartialEquiv := c.toPartialEquiv
    open_source := c.open_source
    open_target := c.open_target
    contMDiffOn_toFun := E.embedding.forward_smooth s hs
    contMDiffOn_invFun := E.embedding.inverse_smooth s hs }
  have hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f (G.exhaustion j) := by
    intro x
    exact (hb x).comp (𝓡 3) X
      (cD.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (himage ⟨x.val, x.property⟩))
  have hinj : InjOn f (G.exhaustion j) := by
    intro x hx y hy hxy
    have hbxy : b x = b y := by
      calc
        b x = E.embedding.inverse s hs (f x) :=
          (E.embedding.left_inverse s hs (himage ⟨x, hx⟩)).symm
        _ = E.embedding.inverse s hs (f y) := congrArg (E.embedding.inverse s hs) hxy
        _ = b y := E.embedding.left_inverse s hs (himage ⟨y, hy⟩)
    have hemb : G.embedding (k + N) x = G.embedding (k + N) y := Subtype.ext hbxy
    have hsub : (⟨x, G.exhaustion_monotone hjk hx⟩ : G.exhaustion (k + N)) =
        ⟨y, G.exhaustion_monotone hjk hy⟩ := (G.embedding_open (k + N)).injective hemb
    exact congrArg Subtype.val hsub
  let : Nonempty G.limitCarrier.carrier := ⟨G.base⟩
  let e := AncientCompactness.partialDiffeomorphOfInjOn (G.exhaustion_open j) f hinj hf
  refine ⟨e, rfl, rfl, rfl, ?_, ?_⟩
  · intro x v w
    have hforward := (E.embedding.forward_smooth s hs (b x.val) (himage x)).contMDiffAt
      (U.isOpen.mem_nhds (himage x))
    have hd := mfderiv_comp x (hforward.mdifferentiableAt (by simp))
      ((hbY x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (fun y : Y => e y.val) x = _ at hd
    rw [hP s hs x v w]
    change _ = q * ((S.flow (G.subsequence (k + N))).metric t).inner (f x.val)
      (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => e y.val) x v)
      (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => e y.val) x w)
    rw [hd]
    rfl
  · intro x
    exact (Cylinder.curvature_of_pullbackFlow (J := J) (U := U) E.embedding
      (fun y : Y => b y.val) hbY himage P hP s hs x).1

end PoincareConjecture.M30
