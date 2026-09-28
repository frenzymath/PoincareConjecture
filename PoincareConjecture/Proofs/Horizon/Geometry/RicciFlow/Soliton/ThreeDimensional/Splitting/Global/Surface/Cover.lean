import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering.Germs
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Small
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory Opposite PoincareConjecture PoincareConjecture.SpaceForm
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem exists_global_inverse_round_surface_local_isometry
    {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (g : RiemannianMetric 2 M)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 2) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        g.leviCivitaData.sectionalCurvature x u v = 1) (p : M) :
    ∃ f : UnitSphere 2 → M, ContMDiff (𝓡 2) (𝓡 2) ∞ f ∧
      ∀ x (v w : TangentSpace (𝓡 2) x),
        (roundSphereMetric 2).inner x v w = g.inner (f x)
          (mfderiv (𝓡 2) (𝓡 2) f x v) (mfderiv (𝓡 2) (𝓡 2) f x w) := by
  let : Nonempty M := ⟨p⟩
  let : SimplyConnectedSpace (UnitSphere 2) :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (by norm_num)
  let : LocallyPathConnectedSpace (UnitSphere 2) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  let q : UnitSphere 2 := ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by simp⟩
  obtain ⟨F, hp, hFq, hF, hFi, hFm⟩ := exists_local_isometry_unitSphere g hsec p q
  have hq : q ∈ F.target := hFq ▸ F.map_source hp
  let U : Opens (TopCat.of (UnitSphere 2)) := ⟨F.target, F.open_target⟩
  let s : (isometryPresheaf (roundSphereMetric 2) g).obj (op U) :=
    ⟨fun x => F.symm x, isometryPredicate_of_map (roundSphereMetric 2) g U F.symm hFi
      (inverse_local_isometry_inner g (roundSphereMetric 2) F hF hFi hFm)⟩
  obtain ⟨t, _⟩ := Poincare.Topology.exists_globalSection_of_locally_bijective_germ
    (isometryPredicate (roundSphereMetric 2) g)
    (locally_bijective_inverse_round_isometry_germ g hsec q) q
    ((isometryPresheaf (roundSphereMetric 2) g).germ U q hq s)
  obtain ⟨ht, htm⟩ := sectionExtension_spec (roundSphereMetric 2) g t.property
  exact ⟨sectionExtension ⊤ t.val, contMDiffOn_univ.mp ht, fun x => htm x (by trivial)⟩



theorem exists_unitSphere_two_covering
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [T3Space M] [ConnectedSpace M] [CompactSpace M]
    (g : RiemannianMetric 2 M)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 2) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        g.leviCivitaData.sectionalCurvature x u v = 1) :
    ∃ q : UnitSphere 2 → M,
      ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧
      ∀ x (u v : TangentSpace (𝓡 2) x),
        g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
          (mfderiv (𝓡 2) (𝓡 2) q x v) = (roundSphereMetric 2).inner x u v := by
  classical
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 2)) M
  let : Small.{0} M := Poincare.Topology.SecondCountable.small M
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (Shrink.{0} M) :=
    Poincare.Manifold.shrinkChartedSpace _ M
  let : IsManifold (𝓡 2) ∞ (Shrink.{0} M) :=
    Poincare.Manifold.shrinkIsManifold (𝓡 2) M
  let : T2Space (Shrink.{0} M) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).t2Space
  let : CompactSpace (Shrink.{0} M) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).compactSpace
  let e := (Poincare.Manifold.shrinkDiffeomorph (𝓡 2) M).symm
  let h := g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph
  have hm (x : Shrink.{0} M) (u v : TangentSpace (𝓡 2) x) :
      h.inner x u v = g.inner (e x)
        (mfderiv (𝓡 2) (𝓡 2) e x u) (mfderiv (𝓡 2) (𝓡 2) e x v) := rfl
  have hs : ∀ (x : Shrink.{0} M) (u v : TangentSpace (𝓡 2) x),
      h.inner x u u * h.inner x v v - (h.inner x u v) ^ 2 ≠ 0 →
        h.leviCivitaData.sectionalCurvature x u v = 1 := by
    intro x u v huv
    have hcurv := h.leviCivitaData.curvatureTensor_eq_of_local_isometry
      g.leviCivitaData isOpen_univ e.contMDiff.contMDiffOn
      (fun y _ a b => hm y a b) (mem_univ x)
    have heq : h.leviCivitaData.sectionalCurvature x u v =
        g.leviCivitaData.sectionalCurvature (e x)
          (mfderiv (𝓡 2) (𝓡 2) e x u) (mfderiv (𝓡 2) (𝓡 2) e x v) := by
      unfold LeviCivitaData.sectionalCurvature
      rw [hcurv]
      rfl
    rw [heq]
    exact hsec (e x) _ _ huv
  let p : M := Classical.choice inferInstance
  obtain ⟨f, hf, hfm⟩ := exists_global_inverse_round_surface_local_isometry h hs (e.symm p)
  let q : UnitSphere 2 → M := e ∘ f
  have hq : ContMDiff (𝓡 2) (𝓡 2) ∞ q := e.contMDiff.comp hf
  have hqm (x : UnitSphere 2) (u v : TangentSpace (𝓡 2) x) :
      g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
        (mfderiv (𝓡 2) (𝓡 2) q x v) = (roundSphereMetric 2).inner x u v := by
    change g.inner (e (f x)) (mfderiv (𝓡 2) (𝓡 2) (e ∘ f) x u)
      (mfderiv (𝓡 2) (𝓡 2) (e ∘ f) x v) = _
    rw [mfderiv_comp x (e.contMDiffAt.mdifferentiableAt (by simp))
      (hf.contMDiffAt.mdifferentiableAt (by simp))]
    exact (hfm x u v).symm
  have hlocal : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q :=
    Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hq fun x =>
      (roundSphereMetric 2).mfderiv_bijective_of_pullback_eq g x (hqm x)
  have hrange : IsClopen (Set.range q) :=
    ⟨(isCompact_range hq.continuous).isClosed, hlocal.isLocalHomeomorph.isOpenMap.isOpen_range⟩
  let : Nonempty (UnitSphere 2) :=
    ⟨⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by simp⟩⟩
  exact ⟨q, hq, Set.range_eq_univ.mp (hrange.eq_univ (Set.range_nonempty q)), hlocal, hqm⟩

end PoincareConjecture.RicciFlow.Splitting
