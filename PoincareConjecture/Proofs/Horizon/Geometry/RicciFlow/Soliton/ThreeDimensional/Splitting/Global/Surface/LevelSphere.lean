import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.SourceProduct
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.LevelInvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.SphereDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem CanonicalAncientRoundProduct.exists_sphere_coordinates_of_reversal
    {F : RicciFlow 3 M (Iic 0)} {r φ : M → ℝ} {κ : ℝ}
    {hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r}
    {hu : HasUnitGradient (F.connection 0) r}
    (hprod : CanonicalAncientRoundProduct F hr hu φ κ)
    (τ : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M) (hτ : Function.Involutive τ)
    (hfree : ∀ x, τ x ≠ x) (hreverse : ∀ x, r (τ x) = -r x)
    (hmetric : ∀ (x : M) (a b : TangentSpace (𝓡 3) x),
      (F.metric 0).inner (τ x) (mfderiv (𝓡 3) (𝓡 3) τ x a)
        (mfderiv (𝓡 3) (𝓡 3) τ x b) = (F.metric 0).inner x a b) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
    letI := openLevelSetChartedSpace hr (⊤ : Opens M) hreg 2 0
    letI := isManifold_openLevelSet hr (⊤ : Opens M) hreg 2 0
    let g := regularLevelMetric hr (⊤ : Opens M) hreg 0 (F.metric 0)
    ∃ s : zeroLevelSet r ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere,
      ∀ x (a b : TangentSpace (𝓡 2) x),
        g.inner x a b = 2 * (roundSphereMetric 2).inner (s x)
          (mfderiv (𝓡 2) (𝓡 2) s x a) (mfderiv (𝓡 2) (𝓡 2) s x b) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  letI := openLevelSetChartedSpace hr (⊤ : Opens M) hreg 2 0
  letI := isManifold_openLevelSet hr (⊤ : Opens M) hreg 2 0
  obtain ⟨hconn, A, _, hA, ⟨cert⟩, hφ, hsol, _⟩ := hprod
  let : ConnectedSpace (zeroLevelSet r) := hconn
  let : CompactSpace (zeroLevelSet r) := cert.compact
  let σ := zeroLevelInvolution hr (regular_of_hasUnitGradient hu) τ hτ hreverse
  have hσ : ∀ x (a b : TangentSpace (𝓡 2) x),
      (A.flow.metric 0).inner (σ x) (mfderiv (𝓡 2) (𝓡 2) σ x a)
        (mfderiv (𝓡 2) (𝓡 2) σ x b) = (A.flow.metric 0).inner x a b := by
    rw [hA]
    exact zeroLevelInvolution_preserves_metric hr (regular_of_hasUnitGradient hu)
      τ hτ hreverse (F.metric 0) hmetric
  obtain ⟨s, hs⟩ := exists_sphereDiffeomorph_of_round_soliton_free_isometry
    (A.flow.connection 0) hφ hsol (cert.round_at_all_times 0 le_rfl) σ hσ
    (zeroLevelInvolution_free hr (regular_of_hasUnitGradient hu) τ hτ hreverse hfree)
  refine ⟨s, ?_⟩
  intro x a b
  exact (congrArg (fun g : RiemannianMetric 2 (zeroLevelSet r) => g.inner x a b) hA).symm.trans
    (hs x a b)

end PoincareConjecture.RicciFlow.Splitting
