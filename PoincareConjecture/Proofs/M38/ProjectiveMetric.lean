import PoincareConjecture.Proofs.M38.ThreeSphereConnection
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Descent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

theorem threeSphereMetric_antipodal (x : UnitThreeSphere)
    (u v : TangentSpace (𝓡 3) x) :
    threeSphereMetric.inner (-x)
      (mfderiv (𝓡 3) (𝓡 3) (Neg.neg : UnitThreeSphere → UnitThreeSphere) x u)
      (mfderiv (𝓡 3) (𝓡 3) (Neg.neg : UnitThreeSphere → UnitThreeSphere) x v) =
      threeSphereMetric.inner x u v := by
  let inc : UnitThreeSphere → EuclideanSpace ℝ (Fin 4) := Subtype.val
  let neg : UnitThreeSphere → UnitThreeSphere := Neg.neg
  have hc := mfderiv_comp x
    ((contMDiff_coe_sphere (n := 3) (m := ∞) (-x)).mdifferentiableAt (by simp))
    ((contMDiff_neg_sphere (n := 3) (m := ∞) x).mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 4) (inc ∘ neg) x =
    (mfderiv (𝓡 3) (𝓡 4) inc (-x)).comp (mfderiv (𝓡 3) (𝓡 3) neg x) at hc
  rw [show inc ∘ neg = -inc from rfl, mfderiv_neg] at hc
  simp only [threeSphereMetric_inner]
  change inner ℝ
    (((mfderiv (𝓡 3) (𝓡 4) inc (-x)).comp (mfderiv (𝓡 3) (𝓡 3) neg x)) u)
    (((mfderiv (𝓡 3) (𝓡 4) inc (-x)).comp (mfderiv (𝓡 3) (𝓡 3) neg x)) v) = _
  rw [← hc]
  simp only [ContinuousLinearMap.neg_apply, inner_neg_neg]
  rfl

variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]

theorem projectiveCover_antipodal_deriv (C : StandardProjectiveSmoothCover Q)
    (x : UnitThreeSphere) :
    (mfderiv (𝓡 3) (𝓡 3) C.cover (-x)).comp
      (mfderiv (𝓡 3) (𝓡 3) (Neg.neg : UnitThreeSphere → UnitThreeSphere) x) =
      mfderiv (𝓡 3) (𝓡 3) C.cover x := by
  have he : C.cover ∘ (Neg.neg : UnitThreeSphere → UnitThreeSphere) = C.cover := by
    funext y
    exact (C.fibers (-y) y).mpr (Or.inr rfl)
  have hc := mfderiv_comp x
    ((C.local_diffeomorph.contMDiff (-x)).mdifferentiableAt (by simp))
    ((contMDiff_neg_sphere (n := 3) (m := ∞) x).mdifferentiableAt (by simp))
  rw [he] at hc
  exact hc.symm

theorem projectiveCover_metric_compatible (C : StandardProjectiveSmoothCover Q)
    (x y : UnitThreeSphere) (hxy : C.cover x = C.cover y)
    (u v : TangentSpace (𝓡 3) x) (u' v' : TangentSpace (𝓡 3) y)
    (hu : mfderiv (𝓡 3) (𝓡 3) C.cover x u = mfderiv (𝓡 3) (𝓡 3) C.cover y u')
    (hv : mfderiv (𝓡 3) (𝓡 3) C.cover x v = mfderiv (𝓡 3) (𝓡 3) C.cover y v') :
    threeSphereMetric.inner x u v = threeSphereMetric.inner y u' v' := by
  have hi (z : UnitThreeSphere) : Function.Injective (mfderiv (𝓡 3) (𝓡 3) C.cover z) :=
    (C.local_diffeomorph.mfderivToContinuousLinearEquiv (by simp) z).injective
  rcases (C.fibers x y).mp hxy with h | h
  · subst y
    rw [hi x hu, hi x hv]
  · subst x
    let A := mfderiv (𝓡 3) (𝓡 3) (Neg.neg : UnitThreeSphere → UnitThreeSphere) y
    have hA (w : TangentSpace (𝓡 3) y) :
        mfderiv (𝓡 3) (𝓡 3) C.cover (-y) (A w) =
          mfderiv (𝓡 3) (𝓡 3) C.cover y w :=
      congrArg (fun L => L w) (projectiveCover_antipodal_deriv C y)
    have heu : u = A u' := hi (-y) (hu.trans (hA u').symm)
    have hev : v = A v' := hi (-y) (hv.trans (hA v').symm)
    rw [heu, hev]
    exact threeSphereMetric_antipodal y u' v'

theorem exists_projectiveMetric (C : StandardProjectiveSmoothCover Q) :
    ∃ g : RiemannianMetric 3 Q,
      ∀ (x : UnitThreeSphere) (u v : TangentSpace (𝓡 3) x),
        threeSphereMetric.inner x u v = g.inner (C.cover x)
          (mfderiv (𝓡 3) (𝓡 3) C.cover x u) (mfderiv (𝓡 3) (𝓡 3) C.cover x v) := by
  obtain ⟨g, hg, _⟩ := Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms
    (A := Unit) (P := fun _ => UnitThreeSphere)
    (fun _ => threeSphereMetric) (fun _ => C.cover) (fun _ => C.local_diffeomorph)
    (fun y => by obtain ⟨x, hx⟩ := C.surjective y; exact ⟨(), x, hx⟩)
    (fun _ _ => projectiveCover_metric_compatible C)
  exact ⟨g, hg ()⟩

noncomputable def projectiveMetric (C : StandardProjectiveSmoothCover Q) :
    RiemannianMetric 3 Q := Classical.choose (exists_projectiveMetric C)

theorem projectiveMetric_inner (C : StandardProjectiveSmoothCover Q)
    (x : UnitThreeSphere) (u v : TangentSpace (𝓡 3) x) :
    threeSphereMetric.inner x u v = (projectiveMetric C).inner (C.cover x)
      (mfderiv (𝓡 3) (𝓡 3) C.cover x u) (mfderiv (𝓡 3) (𝓡 3) C.cover x v) :=
  Classical.choose_spec (exists_projectiveMetric C) x u v

noncomputable def projectiveConnection (C : StandardProjectiveSmoothCover Q) :
    LeviCivitaData (projectiveMetric C) := by
  refine (projectiveMetric C).leviCivitaDataOfCover
    (N := fun _ : Unit => UnitThreeSphere) (fun _ => threeSphereMetric)
    (fun _ => threeSphereConnection) (fun _ => C.cover)
    (fun _ => C.local_diffeomorph.contMDiff) ?_
    (fun _ => projectiveMetric_inner C) ?_
  · intro _ x
    change (C.local_diffeomorph.mfderivToContinuousLinearEquiv
      (by simp) x).toContinuousLinearMap.IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
  · intro y
    obtain ⟨x, hx⟩ := C.surjective y
    exact ⟨(), x, hx⟩

end PoincareConjecture.M38
