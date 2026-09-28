import PoincareConjecture.Proofs.M14.Mathlib.InverseTangentMap
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SectionTransport.TimeBracket

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  (e : MovingSpacetimeGauge F T C) (g : MovingSpacetimeGaugeGeometry e)

theorem movingGauge_inverse_horizontal (t : T.Point) (x : C)
    (V : F.Horizontal (e.toSpacetime (t, x))) :
    (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)).inverse V.val =
      (0, (g.spatialTangentEquiv t x).symm V) := by
  have h := movingGauge_mfderiv_spatial e g t x ((g.spatialTangentEquiv t x).symm V)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [← h]
  exact (movingGauge_mfderiv_isInvertible e (t, x)).inverse_apply_self _

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {L : ModelWithCorners ℝ E H}
  {P : Type w} [TopologicalSpace P] [ChartedSpace H P]

theorem movingGauge_horizontalField_pullback_contMDiffWithinAt
    {b : P → T.Point × C} {Y : ∀ z, F.Horizontal (e.toSpacetime (b z))}
    {S : Set P} {z : P}
    (hb : ContMDiffWithinAt L (spacetimeModel n) ∞ b S z)
    (hY : ContMDiffWithinAt L
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun a => TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (e.toSpacetime (b a)) (Y a)) S z) :
    ContMDiffWithinAt L ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun a => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (b a).2
        ((g.spatialTangentEquiv (b a).1 (b a).2).symm (Y a))) S z := by
  have hi : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (spacetimeModel n).tangent ∞
      (fun v : TotalSpace (EuclideanSpace ℝ (Fin n)) F.Horizontal =>
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) v.proj v.2.val) :=
    F.horizontal_inclusion_smooth
  have htan := (hi.contMDiffAt.comp_contMDiffWithinAt z hY).inverse_mfderiv_apply
    (f := e.toSpacetime) (b := b) (Y := fun a => (Y a).val) hb
    (e.smooth (b z)) (movingGauge_mfderiv_isInvertible e (b z)) (by simp)
  have hproj := (contMDiff_equivTangentBundleProd
    (I := 𝓡∂ 1) (M := T.Point) (I' := 𝓡 n) (M' := C) (n := ∞)).snd
  have h := hproj.contMDiffAt.comp_contMDiffWithinAt z htan
  apply h.congr
  · intro a _
    exact congrArg (fun v : TangentSpace (spacetimeModel n) (b a) =>
      TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : C → Type _)) (b a).2 v.2)
        (movingGauge_inverse_horizontal e g (b a).1 (b a).2 (Y a)).symm
  · exact congrArg (fun v : TangentSpace (spacetimeModel n) (b z) =>
      TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : C → Type _)) (b z).2 v.2)
        (movingGauge_inverse_horizontal e g (b z).1 (b z).2 (Y z)).symm

end PoincareConjecture.M14
