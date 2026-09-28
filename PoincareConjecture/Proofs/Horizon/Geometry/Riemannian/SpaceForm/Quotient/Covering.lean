import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering.Germs
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Small
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Riemannian.SpaceForm

universe u

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_spherical_covering
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [CompactSpace M]
    (g : RiemannianMetric 3 M)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 3) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        g.leviCivitaData.sectionalCurvature x u v = 1) :
    ∃ q : UnitSphere 3 → M,
      ContMDiff (𝓡 3) (𝓡 3) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q ∧
      ∀ x (u v : TangentSpace (𝓡 3) x),
        g.inner (q x) (mfderiv (𝓡 3) (𝓡 3) q x u)
          (mfderiv (𝓡 3) (𝓡 3) q x v) = (roundSphereMetric 3).inner x u v := by
  classical
  let : Small.{0} M := Poincare.Topology.SecondCountable.small M
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Shrink.{0} M) :=
    Poincare.Manifold.shrinkChartedSpace _ M
  let : IsManifold (𝓡 3) ∞ (Shrink.{0} M) :=
    Poincare.Manifold.shrinkIsManifold (𝓡 3) M
  let : T2Space (Shrink.{0} M) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).t2Space
  let : CompactSpace (Shrink.{0} M) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).compactSpace
  let e := (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M).symm
  let h := g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph
  have hm (x : Shrink.{0} M) (u v : TangentSpace (𝓡 3) x) :
      h.inner x u v = g.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x u) (mfderiv (𝓡 3) (𝓡 3) e x v) := rfl
  have hs : ∀ (x : Shrink.{0} M) (u v : TangentSpace (𝓡 3) x),
      h.inner x u u * h.inner x v v - (h.inner x u v) ^ 2 ≠ 0 →
        h.leviCivitaData.sectionalCurvature x u v = 1 := by
    intro x u v huv
    have hcurv := h.leviCivitaData.curvatureTensor_eq_of_local_isometry
      g.leviCivitaData isOpen_univ e.contMDiff.contMDiffOn
      (fun y _ a b => hm y a b) (mem_univ x)
    have heq : h.leviCivitaData.sectionalCurvature x u v =
        g.leviCivitaData.sectionalCurvature (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x u) (mfderiv (𝓡 3) (𝓡 3) e x v) := by
      unfold LeviCivitaData.sectionalCurvature
      rw [hcurv]
      rfl
    rw [heq]
    exact hsec (e x) _ _ huv
  let p : M := Classical.choice inferInstance
  obtain ⟨f, hf, hfm⟩ := exists_global_inverse_round_local_isometry h hs (e.symm p)
  let q : UnitSphere 3 → M := e ∘ f
  have hq : ContMDiff (𝓡 3) (𝓡 3) ∞ q := e.contMDiff.comp hf
  have hqm (x : UnitSphere 3) (u v : TangentSpace (𝓡 3) x) :
      g.inner (q x) (mfderiv (𝓡 3) (𝓡 3) q x u)
        (mfderiv (𝓡 3) (𝓡 3) q x v) = (roundSphereMetric 3).inner x u v := by
    change g.inner (e (f x)) (mfderiv (𝓡 3) (𝓡 3) (e ∘ f) x u)
      (mfderiv (𝓡 3) (𝓡 3) (e ∘ f) x v) = _
    rw [mfderiv_comp x (e.contMDiffAt.mdifferentiableAt (by simp))
      (hf.contMDiffAt.mdifferentiableAt (by simp))]
    exact (hfm x u v).symm
  have hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q :=
    Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hq fun x =>
      (roundSphereMetric 3).mfderiv_bijective_of_pullback_eq g x (hqm x)
  have hrange : IsClopen (Set.range q) :=
    ⟨(isCompact_range hq.continuous).isClosed, hlocal.isLocalHomeomorph.isOpenMap.isOpen_range⟩
  let : Nonempty (UnitSphere 3) :=
    ⟨⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩⟩
  exact ⟨q, hq, Set.range_eq_univ.mp (hrange.eq_univ (Set.range_nonempty q)), hlocal, hqm⟩

end Poincare.Geometry.Riemannian.SpaceForm
