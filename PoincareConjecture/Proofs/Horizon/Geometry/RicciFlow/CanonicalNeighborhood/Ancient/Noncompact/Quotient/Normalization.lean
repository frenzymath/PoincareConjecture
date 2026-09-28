import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem scalarCurvature_cover (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere × ℝ) :
    (K.flow.connection t).scalarCurvature (C.cover p) =
      (C.sphere.connection t).scalarCurvature p.1 := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let e := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := UnitTwoSphere)
  let H := RiemannianMetric.lineProduct (C.sphere.metric t)
  let F : UnitTwoSphere × ℝ → M := C.cover ∘ e.symm
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F :=
    C.cover_local_diffeomorph.contMDiff.comp e.symm.contMDiff
  have hFe : F ∘ e = C.cover := by ext x; simp [F]
  have hfx (x : UnitTwoSphere × ℝ) : F (e x) = C.cover x := congrFun hFe x
  have hd (x : UnitTwoSphere × ℝ)
      (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) x) :
      mfderiv (𝓡 3) (𝓡 3) F (e x)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x a) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.cover x a := by
    rw [← mfderiv_comp_apply x (hF.mdifferentiable (by simp) _)
      (e.contMDiff.mdifferentiable (by simp) _), hFe]
  have hm (y : UnitTwoSphere × ℝ) (a b : TangentSpace (𝓡 3) y) :
      H.inner y a b = (K.flow.metric t).inner (F y)
        (mfderiv (𝓡 3) (𝓡 3) F y a) (mfderiv (𝓡 3) (𝓡 3) F y b) := by
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨a, rfl⟩ := (e.mfderivToContinuousLinearEquiv (by simp) x).surjective a
    obtain ⟨b, rfl⟩ := (e.mfderivToContinuousLinearEquiv (by simp) x).surjective b
    change H.inner (e x)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x a)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x b) =
      (K.flow.metric t).inner (F (e x))
        (mfderiv (𝓡 3) (𝓡 3) F (e x)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x a))
        (mfderiv (𝓡 3) (𝓡 3) F (e x)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x b))
    rw [RiemannianMetric.lineProduct_inner, hd, hd]
    erw [hfx]
    exact (C.metric_transport t ht x a b).symm
  have hs := H.leviCivitaData.scalarCurvature_eq_of_local_isometry
    (K.flow.connection t) isOpen_univ hF.contMDiffOn
    (fun y _ => hm y) (mem_univ (e p))
  rw [hfx] at hs
  exact hs.symm.trans ((C.sphere.metric t).scalarCurvature_eq_of_line_product H
    (C.sphere.connection t) H.leviCivitaData e
    (RiemannianMetric.lineProduct_inner (C.sphere.metric t)) p)

theorem exists_scalarNormalized_sphere (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere × ℝ) :
    0 < (K.flow.connection t).scalarCurvature (C.cover p) ∧
      ∃ a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere,
        ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
          (K.flow.connection t).scalarCurvature (C.cover p) *
            (C.sphere.metric t).inner (a x)
              (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
                2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w := by
  obtain ⟨hpos, q, _, _, hlocal, hmetric, _⟩ :=
    exists_scalarNormalized_roundSurface_cover (C.sphere.metric t)
      (C.sphere.connection t) (C.sphere.round t ht) p.1
  let a := Poincare.Geometry.Manifold.sphereDiffeomorphOfLocalDiffeomorph q hlocal
  rw [C.scalarCurvature_cover ht p]
  exact ⟨hpos, a, hmetric⟩

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
