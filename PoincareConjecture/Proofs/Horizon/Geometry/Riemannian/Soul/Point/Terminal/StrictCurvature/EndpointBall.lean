import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.LocalIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurvePasting

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem toReal_edist_endpoint_le_of_speed_le
    (g : RiemannianMetric n M) {q : ℝ → M} {I : Set ℝ} {C ρ t : ℝ}
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc (0 : ℝ) 1 ⊆ I)
    (hC : 0 < C) (hρC : ρ ≤ C)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1) ≤ C)
    (ht : t ∈ Icc (1 - ρ / C) 1) :
    (g.edist (q t) (q 1)).toReal ≤ ρ := by
  have hleft : 0 ≤ 1 - ρ / C := sub_nonneg.mpr ((div_le_one hC).mpr hρC)
  have hseg : Icc t 1 ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hleft.trans ht.1) le_rfl
  have hd := g.edist_le_of_speed_le_on_Icc hI hq ht.2 (hseg.trans hsub)
    (fun s hs => hspeed s (hseg hs))
  have hr : C * (1 - t) ≤ ρ := by
    have h := (le_div_iff₀ hC).mp (show 1 - t ≤ ρ / C by linarith [ht.1])
    nlinarith
  have hd' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (sub_nonneg.mpr ht.2))] at hd'
  exact hd'.trans hr

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.Conjugate

open ConnectionAlongCurve ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem jacobi_inner_le_sub_endpoint_ball_curvature
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b C κ ρ : ℝ}
    (ha : a < 0) (hb : 1 < b) (hρ : 0 ≤ ρ) (hρC : ρ ≤ C)
    (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I) (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hJ0 : J 0 = 0) (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = C)
    (hmin : g.edist (q 0) (q 1) = ENNReal.ofReal C)
    (hsec : D.NonnegativeSectionalCurvature)
    (hball : ∀ y, (g.edist y (q 1)).toReal ≤ ρ → ∀ u v,
      κ * (g.inner y u u * g.inner y v v - (g.inner y u v) ^ 2) ≤
        D.curvatureTensor y u v u v) :
    g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) ≤
      g.inner (q 1) (J 1) (J 1) -
        κ * (C ^ 2 * g.tangentNorm (q 1) (J 1) ^ 2 -
          (g.inner (q 1) (J 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1)) ^ 2) *
          ((1 - (1 - ρ / C) ^ 3) / 3) := by
  have hs : 1 - ρ / C ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr ((div_le_one hC).mpr hρC), sub_le_self _ (div_nonneg hρ hC.le)⟩
  have h01 : Icc (0 : ℝ) 1 ⊆ I := (Icc_subset_Icc ha.le hb.le).trans hsub
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I :=
    fun t ht => (Realization.contMDiffAt_of_isGeodesicOn hgeo ht).contMDiffWithinAt
  apply jacobi_inner_le_sub_local_curvature_of_minimizing D ha hb hs hI hgeo hsub
    hJ hjac hJ0 hC hspeed hmin hsec
  intro t ht u v hu hv huv
  have hdist := g.toReal_edist_endpoint_le_of_speed_le hI hq h01 hC hρC
    (fun s hs => (hspeed s hs).le) ht
  have h := hball (q t) hdist u v
  simpa [LeviCivitaData.sectionalCurvature, hu, hv, huv] using h

end PoincareConjecture.Conjugate
