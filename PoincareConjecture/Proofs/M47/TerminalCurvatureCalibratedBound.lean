import PoincareConjecture.Proofs.M47.TerminalCurvatureCoverReadouts
import PoincareConjecture.Proofs.M47.TerminalCurvaturePositiveSphere
import PoincareConjecture.Proofs.M47.TerminalCurvatureCalibratedLift
import PoincareConjecture.Statements.Ch04.CurvatureTheory









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting



theorem terminalCurvature_calibrated_null_cover_bound
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u}) (hg : MetricComplete g)
    (hsec : D.NonnegativeSectionalCurvature) (cover : NullOrientationCover D)
    (hrank : ∀ x, ricciNullity D x = 1)
    (hsections : ∀ p : UnitRicciKernel D,
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 3) y),
        IsOpen U ∧ p.val.proj ∈ U ∧
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
        V p.val.proj = p.val.snd ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
          (∀ w, D.ricci y (V y) w = 0) ∧ ∀ w, D.connection V y w = 0)
    (neck : EpsilonNeck g) (hsmall : neck.epsilon ≤ 1 / 200) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  let := unitRicciKernelChartedSpace D cover.covering
  let := unitRicciKernelIsManifold D cover.covering
  let := unitRicciKernelT3Space D cover.covering
  obtain ⟨pf⟩ : Nonempty (unitRicciKernelProjection D ⁻¹' {neck.center}) :=
    (Nat.card_ne_zero.mp (by rw [cover.fiber_card]; norm_num)).1
  let p := pf.val
  let g' := unitRicciKernelMetric D cover.covering
  let W0 := terminalCurvatureOrientedField D cover.covering
  have hg' : MetricComplete g' :=
    unitRicciKernelMetric_complete D cover.covering cover.fiber_card hg
  have hfield := terminalCurvature_oriented_field_geometry D cover.covering hrank hsections
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let gC := g'.connectedComponentMetric p
  let E := gC.leviCivitaData
  let W := mpullback (𝓡 3) (𝓡 3) (Subtype.val : C → UnitRicciKernel D) W0
  let projection := fun q : C => unitRicciKernelProjection D q.val
  have hcomponent := terminalCurvature_component_field g'.leviCivitaData hg' W0 hfield.1
    (fun q => (hfield.2 q).1) (fun q => (hfield.2 q).2) p
  let : ConnectedSpace C := hcomponent.1
  have hread := terminalCurvature_connected_cover_readouts D cover p
  have hmetric (q : C) (v w : TangentSpace (𝓡 3) q) :
      gC.inner q v w = g.inner (projection q)
        (mfderiv (𝓡 3) (𝓡 3) projection q v) (mfderiv (𝓡 3) (𝓡 3) projection q w) :=
    (hread q).1 v w
  have hsecC : E.NonnegativeSectionalCurvature := by
    intro q v w
    rw [(hread q).2.1 v w]
    exact hsec _ _ _
  have hproj := unitRicciKernelComponent_projection_isLocalDiffeomorph D cover.covering p
  have hsurj := unitRicciKernelComponent_projection_surjective D cover.covering cover.fiber_card p
  have hcover := unitRicciKernelComponent_projection_isCoveringMap D
    cover.covering cover.fiber_card p
  let theta0 := (neck.coordinate_inverse neck.center).1
  let : Nonempty UnitTwoSphere := ⟨theta0⟩
  obtain ⟨q0, hq0⟩ := hsurj (neck.coordinate_map (theta0, 0))
  obtain ⟨F, hF, _, _, _, _, hplane⟩ := terminalCurvature_lifted_calibrated_neck_sphere
    D E projection hcover hproj hmetric neck hsmall theta0 q0 hq0
  obtain ⟨B, hB, hbound⟩ := terminalCurvature_bounded_of_parallel_positive_sphere
    E (hC.tensor_calculus 3 C gC E) hcomponent.2.1 hsecC W hcomponent.2.2.1
    (fun q => (hcomponent.2.2.2 q).2.1) (fun q => (hcomponent.2.2.2 q).2.2)
    (fun q => (hread q).2.2.1) F hF hplane
  refine ⟨B, hB, ?_⟩
  intro x
  obtain ⟨q, rfl⟩ := hsurj x
  exact (hread q).2.2.2 ▸ hbound q

end PoincareConjecture.M47
