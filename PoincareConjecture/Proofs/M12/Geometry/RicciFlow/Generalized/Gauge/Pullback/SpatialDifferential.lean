import PoincareConjecture.Definitions.M12MovingGauge
import Mathlib.Topology.VectorBundle.FiniteDimensional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.MovingSpacetimeGauge

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

theorem spatial_mfderiv_eq (e : MovingSpacetimeGauge F T C)
    (t : T.Point) (x : C) (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) (spacetimeModel n) (fun y => e.toSpacetime (t, y)) x v =
      mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x) (0, v) := by
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))
  letI : NormedSpace ℝ (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))
  letI : NormedAddCommGroup (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  letI : NormedSpace ℝ (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  have h := mfderiv_prod_eq_add_apply (p := (t, x))
    (e.smooth.mdifferentiableAt (by simp)) (v := (0, v))
  simpa only [map_zero, zero_add] using h.symm

theorem spatial_mfderiv_horizontal (e : MovingSpacetimeGauge F T C)
    (t : T.Point) (x : C) (v : TangentSpace (𝓡 n) x) :
    mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction (e.toSpacetime (t, x))
      (mfderiv (𝓡 n) (spacetimeModel n) (fun y => e.toSpacetime (t, y)) x v) = 0 := by
  have hs : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y => e.toSpacetime (t, y)) :=
    e.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have heq : (F.timeFunction ∘ (fun y : C => e.toSpacetime (t, y))) =
      fun _ => t.val := funext fun y => e.time_eq (t, y)
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ F.timeFunction := F.time_smooth
  have h := mfderiv_comp_apply (x := x)
    (ht.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp)) v
  rw [heq, mfderiv_const] at h
  exact h.symm

def spatialDifferential (e : MovingSpacetimeGauge F T C) (t : T.Point) (x : C) :
    TangentSpace (𝓡 n) x →L[ℝ] F.Horizontal (e.toSpacetime (t, x)) :=
  (F.horizontalProjection (e.toSpacetime (t, x))).comp
    (mfderiv (𝓡 n) (spacetimeModel n) (fun y => e.toSpacetime (t, y)) x)

theorem spatialDifferential_val (e : MovingSpacetimeGauge F T C)
    (t : T.Point) (x : C) (v : TangentSpace (𝓡 n) x) :
    (e.spatialDifferential t x v).val =
      mfderiv (𝓡 n) (spacetimeModel n) (fun y => e.toSpacetime (t, y)) x v := by
  let w : F.Horizontal (e.toSpacetime (t, x)) :=
    ⟨mfderiv (𝓡 n) (spacetimeModel n) (fun y => e.toSpacetime (t, y)) x v,
      e.spatial_mfderiv_horizontal t x v⟩
  exact congrArg Subtype.val (F.horizontalProjection_identity _ w)

theorem spatialDifferential_injective (e : MovingSpacetimeGauge F T C)
    (t : T.Point) (x : C) : Function.Injective (e.spatialDifferential t x) := by
  intro v w hvw
  have h := congrArg Subtype.val hvw
  rw [e.spatialDifferential_val, e.spatialDifferential_val,
    e.spatial_mfderiv_eq, e.spatial_mfderiv_eq] at h
  exact congrArg Prod.snd (e.differential_injective (t, x) h)

def spatialTangentEquiv (e : MovingSpacetimeGauge F T C) (t : T.Point) (x : C) :
    TangentSpace (𝓡 n) x ≃L[ℝ] F.Horizontal (e.toSpacetime (t, x)) := by
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  letI : NormedSpace ℝ (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  letI := VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
    F.Horizontal (e.toSpacetime (t, x))
  exact (LinearEquiv.ofInjectiveOfFinrankEq (e.spatialDifferential t x).toLinearMap
    (e.spatialDifferential_injective t x)
    (VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)) F.Horizontal _).symm).toContinuousLinearEquiv

theorem spatialTangentEquiv_val (e : MovingSpacetimeGauge F T C)
    (t : T.Point) (x : C) (v : TangentSpace (𝓡 n) x) :
    (e.spatialTangentEquiv t x v).val =
      mfderiv (𝓡 n) (spacetimeModel n) (fun y => e.toSpacetime (t, y)) x v :=
  e.spatialDifferential_val t x v

end

end PoincareConjecture.MovingSpacetimeGauge
