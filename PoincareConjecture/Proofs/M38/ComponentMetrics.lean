import PoincareConjecture.Proofs.M38.ProjectiveCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M38

variable {M Q : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ Q]

noncomputable def metricAlongDiffeomorph (g : RiemannianMetric 3 Q)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M Q ∞) : RiemannianMetric 3 M :=
  g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph

theorem metricAlongDiffeomorph_inverse_inner (g : RiemannianMetric 3 Q)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M Q ∞) (y : Q)
    (u v : TangentSpace (𝓡 3) y) :
    g.inner y u v = (metricAlongDiffeomorph g e).inner (e.symm y)
      (mfderiv (𝓡 3) (𝓡 3) e.symm y u) (mfderiv (𝓡 3) (𝓡 3) e.symm y v) := by
  have heq : e ∘ e.symm = id := funext e.apply_symm_apply
  have hd := mfderiv_comp y
    ((e.contMDiff (e.symm y)).mdifferentiableAt (by simp))
    ((e.symm.contMDiff y).mdifferentiableAt (by simp))
  rw [heq, mfderiv_id] at hd
  have hderiv (w : TangentSpace (𝓡 3) y) :
      mfderiv (𝓡 3) (𝓡 3) e (e.symm y)
        (mfderiv (𝓡 3) (𝓡 3) e.symm y w) = w := by
    exact (congrArg (fun L => L w) hd).symm
  change g.inner y u v = g.inner (e (e.symm y))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y u))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v))
  rw [hderiv, hderiv, e.apply_symm_apply]

noncomputable def connectionAlongDiffeomorph {g : RiemannianMetric 3 Q}
    (D : LeviCivitaData g) (e : Diffeomorph (𝓡 3) (𝓡 3) M Q ∞) :
    LeviCivitaData (metricAlongDiffeomorph g e) := by
  refine (metricAlongDiffeomorph g e).leviCivitaDataOfCover
    (N := fun _ : Unit => Q) (fun _ => g) (fun _ => D) (fun _ => e.symm)
    (fun _ => e.symm.contMDiff) ?_
    (fun _ => metricAlongDiffeomorph_inverse_inner g e) ?_
  · intro _ y
    change (e.symm.isLocalDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) y).toContinuousLinearMap.IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
  · intro x
    exact ⟨(), e x, e.symm_apply_apply x⟩

theorem positiveCurvatureAlongDiffeomorph {g : RiemannianMetric 3 Q}
    (D : LeviCivitaData g) (e : Diffeomorph (𝓡 3) (𝓡 3) M Q ∞)
    (hround : ConstantPositiveSectionalCurvature g D) :
    ConstantPositiveSectionalCurvature (metricAlongDiffeomorph g e)
      (connectionAlongDiffeomorph D e) := by
  obtain ⟨c, hc, hcurv⟩ := hround
  refine ⟨c, hc, ?_⟩
  intro x u v hu hv huv
  have ht := (connectionAlongDiffeomorph D e).curvatureTensor_eq_of_local_isometry
    D isOpen_univ e.contMDiff.contMDiffOn (fun _ _ _ _ => rfl)
    (Set.mem_univ x) u v u v
  have hu' : g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
      (mfderiv (𝓡 3) (𝓡 3) e x u) = 1 := hu
  have hv' : g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
      (mfderiv (𝓡 3) (𝓡 3) e x v) = 1 := hv
  have huv' : g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
      (mfderiv (𝓡 3) (𝓡 3) e x v) = 0 := huv
  calc
    (connectionAlongDiffeomorph D e).sectionalCurvature x u v =
        D.sectionalCurvature (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v) := by
      simp only [LeviCivitaData.sectionalCurvature, ht]
      rfl
    _ = c := hcurv (e x) _ _ hu' hv' huv'

end PoincareConjecture.M38
