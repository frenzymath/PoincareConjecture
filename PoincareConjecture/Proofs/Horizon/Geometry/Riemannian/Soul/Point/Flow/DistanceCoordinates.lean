import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.RadiusReparametrization












noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric.RadialHomeomorph

variable {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {p : M}

private theorem distance_pos_off_center (x : {x : M // x ≠ p}) :
    0 < (g.edist p x).toReal := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  exact ENNReal.toReal_pos (ne_of_gt (edist_pos.mpr x.property.symm))
    (g.edist_ne_top p x)



def of_monotone_trajectories
    (F : (UnitTwoSphere × Ioi (0 : ℝ)) ≃ₜ {x : M // x ≠ p})
    (hmono : ∀ theta, StrictMono
      (fun t : Ioi (0 : ℝ) => (g.edist p (F (theta, t))).toReal))
    (hsurj : ∀ theta r, 0 < r → ∃ t : Ioi (0 : ℝ),
      (g.edist p (F (theta, t))).toReal = r) : RadialHomeomorph g p := by
  let f : UnitTwoSphere × Ioi (0 : ℝ) → Ioi (0 : ℝ) :=
    fun z => ⟨(g.edist p (F z)).toReal, distance_pos_off_center (F z)⟩
  have hf : Continuous f :=
    ((g.continuous_toReal_edist p).comp
      (continuous_subtype_val.comp F.continuous)).subtype_mk _
  have hfm : ∀ theta, StrictMono (fun t => f (theta, t)) := fun theta => hmono theta
  have hfs : ∀ theta, Function.Surjective (fun t => f (theta, t)) := by
    intro theta r
    obtain ⟨t, ht⟩ := hsurj theta r r.property
    exact ⟨t, Subtype.ext ht⟩
  let K := Poincare.Topology.positiveRadiusReparametrization f hf hfm hfs
  refine ⟨K.symm.trans F, ?_⟩
  intro z
  have h := congrArg (fun w : UnitTwoSphere × Ioi (0 : ℝ) => (w.2 : ℝ))
    (K.apply_symm_apply z)
  exact h

end PoincareConjecture.RiemannianMetric.RadialHomeomorph
