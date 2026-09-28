import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.Variation.Index
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Sectional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.Synge

open ConnectionAlongCurve ConnectionVariation ConjugateVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {γ η₀ η₁ : ℝ → M}
  {V : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}

theorem intrinsicIndexIntegrand_neg_of_parallel
    (D : LeviCivitaData g) {t : ℝ}
    (hsec : ∀ u v, g.inner (γ t) u u = 1 → g.inner (γ t) v v = 1 →
      g.inner (γ t) u v = 0 → 0 < D.sectionalCurvature (γ t) u v)
    (hparallel : manifoldCovDerivAlong g γ V 1 t = 0)
    (hind : LinearIndependent ℝ ![V t, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1]) :
    intrinsicIndexIntegrand g D γ V t < 0 := by
  have h := D.curvatureTensor_diagonal_pos_of_orthonormal (γ t) hsec hind
  simpa only [intrinsicIndexIntegrand, hparallel, map_zero, zero_apply, zero_sub,
    LeviCivitaData.curvatureTensor, neg_lt_zero] using h

theorem GeodesicVariation.sum_index_neg [T2Space M]
    (R : GeodesicVariation g γ V a b η₀ η₁) (D : LeviCivitaData g)
    {I : Set ℝ} (hsub : Icc a b ⊆ I) (hgeo : g.IsGeodesicOn γ I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    (hsec : ∀ t ∈ Icc a b, ∀ u v,
      g.inner (γ t) u u = 1 → g.inner (γ t) v v = 1 →
      g.inner (γ t) u v = 0 → 0 < D.sectionalCurvature (γ t) u v)
    (hparallel : ∀ t ∈ Icc a b, manifoldCovDerivAlong g γ V 1 t = 0)
    (hind : ∀ t ∈ Icc a b,
      LinearIndependent ℝ ![V t, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1]) :
    (∑ i ∈ Finset.range R.N, ∫ t in (R.τ i)..(R.τ (i + 1)),
      intrinsicIndexIntegrand g D γ V t) < 0 := by
  have hneg (i : ℕ) (hi : i ∈ Finset.range R.N) :
      (∫ t in (R.τ i)..(R.τ (i + 1)), intrinsicIndexIntegrand g D γ V t) < 0 := by
    have hi' := Finset.mem_range.mp hi
    have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on
      (R.index_integrable D hsub hgeo hV i hi').neg
      (fun t ht => neg_pos.mpr (intrinsicIndexIntegrand_neg_of_parallel D
        (hsec t (R.time_subset hi' (Ioo_subset_Icc_self ht)))
        (hparallel t (R.time_subset hi' (Ioo_subset_Icc_self ht)))
        (hind t (R.time_subset hi' (Ioo_subset_Icc_self ht))))) (R.strict i)
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg, neg_pos] using hpos
  exact Finset.sum_neg (fun i hi => hneg i hi)
    ⟨0, Finset.mem_range.mpr R.N_pos⟩

theorem not_minimizing_endpoints_of_parallel [T2Space M]
    (D : LeviCivitaData g) {I : Set ℝ}
    (hab : a < b) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hgeo : g.IsGeodesicOn γ I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    (hsec : ∀ t ∈ Icc a b, ∀ u v,
      g.inner (γ t) u u = 1 → g.inner (γ t) v v = 1 →
      g.inner (γ t) u v = 0 → 0 < D.sectionalCurvature (γ t) u v)
    (hparallel : ∀ t ∈ Icc a b, manifoldCovDerivAlong g γ V 1 t = 0)
    (hind : ∀ t ∈ Icc a b,
      LinearIndependent ℝ ![V t, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1])
    {δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁)
    (hη₀ : g.IsGeodesicOn η₀ (Ioo (-δ₀) δ₀))
    (hη₁ : g.IsGeodesicOn η₁ (Ioo (-δ₁) δ₁))
    (hη₀0 : η₀ 0 = γ a) (hη₁0 : η₁ 0 = γ b)
    (hη₀v : HasDerivAt (fun s => extChartAt (𝓡 n) (γ a) (η₀ s)) (V a) 0)
    (hη₁v : HasDerivAt (fun s => extChartAt (𝓡 n) (γ b) (η₁ s)) (V b) 0)
    {C : ℝ} (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc a b, g.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = C) :
    ¬ ∀ᶠ s in 𝓝 (0 : ℝ),
      ENNReal.ofReal ((b - a) * C) ≤ g.edist (η₀ s) (η₁ s) := by
  intro hmin
  obtain ⟨R⟩ := exists_geodesicVariation g hab hI hsub hgeo hV
    hδ₀ hδ₁ hη₀ hη₁ hη₀0 hη₁0 hη₀v hη₁v
  exact (not_lt_of_ge (R.sum_index_nonneg D hsub hgeo hV hC hspeed hmin))
    (R.sum_index_neg D hsub hgeo hV hsec hparallel hind)

end PoincareConjecture.Synge
