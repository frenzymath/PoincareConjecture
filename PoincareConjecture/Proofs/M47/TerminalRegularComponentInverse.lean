import PoincareConjecture.Proofs.M47.TerminalRegularNormalMaps
import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialInverse
import PoincareConjecture.Proofs.M04.ShiCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSource_regular_component_inverse
    {F : SurgeryFlowData.{u}} {base Q tau A : ℝ}
    (center : (F.slice base).carrier) :
    let U : TopologicalSpace.Opens (F.slice base).carrier :=
      ⟨(F.metric base).ball center (A / Real.sqrt Q), M04.initial_ball_isOpen _ _ _⟩
    ∀ (p0 : U), p0.val = center →
    ∀ (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau) 0) U)
      (h0 : (0 : ℝ) ∈ Icc (-tau) 0) (g : RiemannianMetric 3 U),
    let j := terminalSourceNormal_terminalMap U p0 e h0
    (∀ z : U, j z = z.val) →
    (∀ z (v w : TangentSpace (𝓡 3) z), g.inner z v w = Q * (F.metric base).inner (j z)
      (mfderiv (𝓡 3) (𝓡 3) j z v) (mfderiv (𝓡 3) (𝓡 3) j z w)) →
    let h : RiemannianMetric 3 (F.slice base).carrier :=
      M13.scaleSmoothMetric (F.metric base) Q e.scale_pos
    let C := Poincare.connectedComponentOpens E center
    let p : C := ⟨center, mem_connectedComponent⟩
    letI := terminalSourceComponentMetricSpace h center
    ∃ jC : PartialDiffeomorph (𝓡 3) (𝓡 3) U C ∞,
      jC.source = univ ∧ jC.target = Metric.ball p A ∧
      (∀ z : U, (jC z).val = z.val) ∧ jC p0 = p ∧
      ∀ z (v w : TangentSpace (𝓡 3) z),
        g.inner z v w = (h.connectedComponentMetric center).inner (jC z)
          (mfderiv (𝓡 3) (𝓡 3) jC z v) (mfderiv (𝓡 3) (𝓡 3) jC z w) := by
  let U : TopologicalSpace.Opens (F.slice base).carrier :=
    ⟨(F.metric base).ball center (A / Real.sqrt Q), M04.initial_ball_isOpen _ _ _⟩
  dsimp only
  intro p0 hp0 e h0 g hmap hmetric
  let j := terminalSourceNormal_terminalMap U p0 e h0
  let h : RiemannianMetric 3 (F.slice base).carrier :=
    M13.scaleSmoothMetric (F.metric base) Q e.scale_pos
  let C := Poincare.connectedComponentOpens E center
  let p : C := ⟨center, mem_connectedComponent⟩
  let : MetricSpace C := terminalSourceComponentMetricSpace h center
  let : Nonempty U := ⟨p0⟩
  have hjfun : (j : U → (F.slice base).carrier) = Subtype.val := funext hmap
  have hball (z : U) : z.val ∈ h.ball center A := by
    rw [terminalSourceNormal_scaled_ball]
    exact z.property
  let f := terminalSourceComponentMap h center (Subtype.val : U → (F.slice base).carrier) hball
  have hs : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : U → (F.slice base).carrier) :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U
  have hf := terminalSourceComponentMap_geometry h center
    (Subtype.val : U → (F.slice base).carrier) hball U.isOpen.isOpenEmbedding_subtypeVal hs
  obtain ⟨jC, hjC, hsource, htarget⟩ := terminalCurvature_exists_actual_partial_inverse
    (f := f) isOpen_univ (hf.1.comp isOpen_univ.isOpenEmbedding_subtypeVal)
      (hf.2.isLocalDiffeomorphOn univ)
  have himage : f '' univ = Metric.ball p A := by
    ext y
    constructor
    · rintro ⟨z, _, rfl⟩
      have hz : (f z).val ∈ (Subtype.val : C → (F.slice base).carrier) '' Metric.ball p A := by
        rw [(terminalSourceComponent_balls h center p A).2.1]
        exact hball z
      obtain ⟨w, hw, heq⟩ := hz
      exact (Subtype.ext heq : w = f z) ▸ hw
    · intro hy
      have hyh : y.val ∈ h.ball center A := by
        rw [← (terminalSourceComponent_balls h center p A).2.1]
        exact ⟨y, hy, rfl⟩
      have hyU : y.val ∈ U := by
        rwa [terminalSourceNormal_scaled_ball] at hyh
      exact ⟨⟨y.val, hyU⟩, mem_univ _, Subtype.ext rfl⟩
  refine ⟨jC, hsource, htarget.trans himage, ?_, ?_, ?_⟩
  · intro z
    rw [hjC]
    rfl
  · apply Subtype.ext
    rw [hjC]
    exact hp0
  · intro z v w
    rw [hjC, terminalSourceComponentMap_metric h center
      (Subtype.val : U → (F.slice base).carrier) hball hs]
    have hm := hmetric z v w
    change g.inner z v w = Q * (F.metric base).inner (j z)
      (mfderiv (𝓡 3) (𝓡 3) j z v) (mfderiv (𝓡 3) (𝓡 3) j z w) at hm
    rw [hjfun] at hm
    exact hm

end PoincareConjecture.M47
