import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.FixedChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.SmoothDeck









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ}



theorem IsGeodesicOn.comp_local_isometry
    {g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : EuclideanSpace ℝ (Fin n),
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {I : Set ℝ}
    (hγ : g.IsGeodesicOn γ I) (hI : IsOpen I) (hγU : MapsTo γ I U) :
    h.IsGeodesicOn (f ∘ γ) I := by
  have hcoeff (k : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
      k.pullbackCoefficients id = k.euclideanCoefficients := by
    ext x a b
    simp only [pullbackCoefficients, mfderiv_id, euclideanCoefficients]
    rfl
  have hode (t : ℝ) (ht : t ∈ I) :
      HasDerivAt γ (deriv γ t) t ∧ HasDerivAt (deriv γ)
        (-coordinateChristoffel g.euclideanCoefficients (γ t) (deriv γ t) (deriv γ t)) t := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, hcoeff, id_eq] using
      hγ.hasDerivAt_in_chart hI (γ t) (by simp) t ht
  intro t ht
  refine ⟨0, f ∘ γ, (fun s => fderiv ℝ f (γ s) (deriv γ s)), ?_⟩
  filter_upwards [hI.mem_nhds ht] with s hs
  have hfs := (hf _ (hγU hs)).contMDiffAt (hU.mem_nhds (hγU hs))
  have hm : ∀ᶠ y in 𝓝 (γ s), ∀ a b,
      g.euclideanCoefficients y a b = h.euclideanCoefficients (f y)
        (fderiv ℝ f y a) (fderiv ℝ f y b) := by
    filter_upwards [hU.mem_nhds (hγU hs)] with y hy a b
    have hh := hmetric y hy a b
    rw [mfderiv_eq_fderiv] at hh
    convert! hh using 1
  have hsurj : Function.Surjective (fderiv ℝ f (γ s)) := by
    have hb := g.mfderiv_bijective_of_pullback_eq h (γ s)
      (fun a b => (hmetric _ (hγU hs) a b).symm)
    rw [mfderiv_eq_fderiv] at hb
    convert! hb.2 using 1
  have htrans := hasDerivAt_geodesic_change_coordinates
    ((g.contDiffAt_euclideanCoefficients (γ s)).differentiableAt (by simp))
    ((h.contDiffAt_euclideanCoefficients (f (γ s))).differentiableAt (by simp))
    (g.inner_isInvertible _) (h.inner_isInvertible _) (h.symm _)
    (contMDiffAt_iff_contDiffAt.mp hfs) hsurj hm (hode s hs).1 (hode s hs).2
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, PartialEquiv.refl_target, mem_univ, id_eq,
    hcoeff, Function.comp_apply, true_and]
  exact htrans

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem inner_deck_motion_of_pullback
    (G : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e (d x))
    (hd : DifferentiableAt ℝ d x) (hproj : (e ∘ d) =ᶠ[𝓝 x] e)
    (hGx : G.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGdx : G.euclideanCoefficients (d x) = g.pullbackCoefficients e (d x))
    (a b : EuclideanSpace ℝ (Fin n)) :
    G.inner x a b = G.inner (d x)
      (mfderiv (𝓡 n) (𝓡 n) d x a) (mfderiv (𝓡 n) (𝓡 n) d x b) := by
  have hm := pullbackCoefficients_deck_motion g he hd hproj a b
  rw [← hGx, ← hGdx] at hm
  rw [mfderiv_eq_fderiv]
  convert! hm.symm using 1

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem curvatureTensorNorm_eq_of_pullback_germ
    {G : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n M} (DG : LeviCivitaData G) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x)
    (hcoeff : G.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e) :
    DG.curvatureTensorNorm x = D.curvatureTensorNorm (e x) := by
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : EuclideanSpace ℝ (Fin n),
      G.inner y a b = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y a) (mfderiv (𝓡 n) (𝓡 n) e y b) := by
    filter_upwards [hcoeff] with y hy a b
    exact congrArg (fun B => B a b) hy
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible := by
    filter_upwards [hmetric] with y hy
    have hb := G.mfderiv_bijective_of_pullback_eq g y (fun a b => (hy a b).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) := by
      unfold TangentSpace
      infer_instance
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (e y)) := by
      unfold TangentSpace
      infer_instance
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 n) (𝓡 n) e y).toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  exact DG.curvatureTensorNorm_eq_pullback_euclidean D he hinv hmetric

end PoincareConjecture.LeviCivitaData
