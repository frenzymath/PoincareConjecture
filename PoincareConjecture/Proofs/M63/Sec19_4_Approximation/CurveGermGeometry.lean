import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {gamma delta : ℝ → M} {x : ℝ}

theorem curveSpeed_congr_germ (F : RicciFlow n M (Set.Icc a b)) (t : ℝ)
    (h : gamma =ᶠ[𝓝 x] delta) :
    curveSpeed F (fun y _ => gamma y) t x = curveSpeed F (fun y _ => delta y) t x := by
  have hvelocity : curveVelocity (n := n) gamma x = curveVelocity (n := n) delta x := by
    unfold curveVelocity
    rw [h.mfderiv_eq]
    rfl
  change (F.metric t).tangentNorm (gamma x) (curveVelocity gamma x) =
    (F.metric t).tangentNorm (delta x) (curveVelocity delta x)
  rw [hvelocity, h.eq_of_nhds]

theorem pullback_jet_congr_germ {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {Y : (s : ℝ) → TangentSpace (𝓡 n) (gamma s)}
    {Z : (s : ℝ) → TangentSpace (𝓡 n) (delta s)}
    (h : (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 n) M)) =ᶠ[𝓝 x]
      (fun s => (⟨delta s, Z s⟩ : TangentBundle (𝓡 n) M))) :
    (⟨gamma x, rampHorizontalCovariantDerivative D gamma Y x⟩ : TangentBundle (𝓡 n) M) =
      (⟨delta x, rampHorizontalCovariantDerivative D delta Z x⟩ :
        TangentBundle (𝓡 n) M) := by
  have hbase : gamma =ᶠ[𝓝 x] delta :=
    h.mono (fun _ hs => congrArg (fun z : TangentBundle (𝓡 n) M => z.proj) hs)
  have hpoint : gamma x = delta x := hbase.eq_of_nhds
  have hfield : Y x = Z x :=
    congrArg (fun z : TangentBundle (𝓡 n) M => z.2) h.eq_of_nhds
  have hvelocity : curveVelocity (n := n) gamma x = curveVelocity (n := n) delta x := by
    unfold curveVelocity
    rw [hbase.mfderiv_eq]
    rfl
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (delta x)
  have hcoords : (fun s => (e ⟨gamma s, Y s⟩).2) =ᶠ[𝓝 x]
      (fun s => (e ⟨delta s, Z s⟩).2) :=
    h.mono (fun _ hs => congrArg (fun z : TangentBundle (𝓡 n) M => (e z).2) hs)
  have hderiv : rampHorizontalCovariantDerivative D gamma Y x =
      rampHorizontalCovariantDerivative D delta Z x := by

    let K (q : M) (y v w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) q).symmL ℝ q w +
        D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (x := q) y) q v
    change K (gamma x) (Y x) (curveVelocity gamma x)
      (deriv (fun s => ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) (gamma x)) ⟨gamma s, Y s⟩).2) x) =
      K (delta x) (Z x) (curveVelocity delta x) (deriv (fun s => (e ⟨delta s, Z s⟩).2) x)
    rw [hpoint, hfield, hvelocity, hcoords.deriv_eq]
  apply TotalSpace.ext hpoint
  exact heq_of_eq hderiv

theorem curvature_congr_germ (F : RicciFlow n M (Set.Icc a b)) (t : ℝ)
    (h : gamma =ᶠ[𝓝 x] delta) :
    m62Curvature F (fun y _ => gamma y) t x = m62Curvature F (fun y _ => delta y) t x := by
  have hunit :
      (fun s => (⟨gamma s, spatialUnitTangent F (fun y _ => gamma y) t s⟩ :
        TangentBundle (𝓡 n) M)) =ᶠ[𝓝 x]
      (fun s => (⟨delta s, spatialUnitTangent F (fun y _ => delta y) t s⟩ :
        TangentBundle (𝓡 n) M)) := by
    filter_upwards [h.eventuallyEq_nhds] with s hs
    apply TotalSpace.ext hs.eq_of_nhds
    apply heq_of_eq
    have hvelocity : curveVelocity (n := n) gamma s = curveVelocity (n := n) delta s := by
      unfold curveVelocity
      rw [hs.mfderiv_eq]
      rfl
    change (curveSpeed F (fun y _ => gamma y) t s)⁻¹ • curveVelocity gamma s =
      (curveSpeed F (fun y _ => delta y) t s)⁻¹ • curveVelocity delta s
    rw [curveSpeed_congr_germ F t hs, hvelocity]
  have hpull := pullback_jet_congr_germ (F.connection t) hunit
  have hvalue := congrArg (fun z : TangentBundle (𝓡 n) M => z.2) hpull
  change rampHorizontalCovariantDerivative (F.connection t) gamma
    (spatialUnitTangent F (fun y _ => gamma y) t) x =
      rampHorizontalCovariantDerivative (F.connection t) delta
        (spatialUnitTangent F (fun y _ => delta y) t) x at hvalue
  unfold m62Curvature m62CurvatureSquared m62CurvatureVector m62SpatialDerivative
  dsimp only
  rw [curveSpeed_congr_germ F t h, hvalue, h.eq_of_nhds]

end PoincareConjecture.M63
