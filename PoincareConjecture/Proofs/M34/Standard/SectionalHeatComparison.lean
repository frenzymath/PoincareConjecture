import PoincareConjecture.Proofs.M34.Standard.SectionalModelParameters
import PoincareConjecture.Proofs.M34.Standard.SectionalBarrierVelocity
import PoincareConjecture.Proofs.M34.Standard.SectionalScalarLower
import PoincareConjecture.Proofs.M04.CompactSlabParabolic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.M10.LaplacianLinearity










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open M04




theorem sectional_ge_heat_subsolution_on_compact
    {J : Set ℝ} {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) J) (hJ : Icc a b ⊆ J)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (B V : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hB : ContinuousOn (Function.uncurry B) (Icc a b ×ˢ K))
    (hsmooth : ∀ t ∈ Icc a b, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (B t))
    (hderiv : ∀ t ∈ Icc a b, ∀ x ∈ K,
      HasDerivWithinAt (fun s => B s x) (V t x) (Icc a b) t)
    (hevol : ∀ t ∈ Ioc a b, ∀ x ∈ interior K,
      V t x ≤ (F.connection t).laplacian (B t) x)
    (hboundary : ∀ t ∈ Icc a b, ∀ x ∈ K \ interior K, B t x ≤ 0)
    (hnonneg : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hinit : ∀ x ∈ K, ∀ p ∈ modelOrthonormalPairs 3,
      B a x ≤ (F.connection a).curvatureTensor x p.1 p.2 p.1 p.2 /
        metricGram (F.metric a) x p.1 p.2) :
    ∀ t ∈ Icc a b, ∀ x ∈ K, ∀ p ∈ modelOrthonormalPairs 3,
      B t x ≤ (F.connection t).curvatureTensor x p.1 p.2 p.1 p.2 /
        metricGram (F.metric t) x p.1 p.2 := by
  let E := EuclideanSpace ℝ (Fin 3)
  let S := K ×ˢ modelOrthonormalPairs 3
  let q := fun t (z : E × (E × E)) =>
    (F.connection t).curvatureTensor z.1 z.2.1 z.2.2 z.2.1 z.2.2 /
      metricGram (F.metric t) z.1 z.2.1 z.2.2
  let w := fun t (z : E × (E × E)) => q t z - B t z.1
  let velocity := fun t (z : E × (E × E)) =>
    sectionalRayleighVelocity (F.connection t) z.1 z.2.1 z.2.2 - V t z.1
  have hgram (t : ℝ) (z : E × (E × E)) (hz : z ∈ S) :
      0 < metricGram (F.metric t) z.1 z.2.1 z.2.2 :=
    metricGram_pos_of_linearIndependent _ _ _ _ (modelOrthonormalPairs_linearIndependent hz.2)
  have hq0 (t : ℝ) (ht : t ∈ Icc a b) (z : E × (E × E)) (hz : z ∈ S) :
      0 ≤ q t z := div_nonneg (hnonneg t ht z.1 z.2.1 z.2.2) (hgram t z hz).le
  have hw : ContinuousOn (Function.uncurry w) (Icc a b ×ˢ S) := by
    apply ((continuousOn_flow_sectionalRayleigh_model F).mono
      (prod_mono hJ (prod_mono (subset_univ K) (Subset.refl _)))).sub
    exact hB.comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
      (fun z hz => ⟨hz.1, hz.2.1⟩)
  have hd : ∀ t ∈ Icc a b, ∀ z ∈ S,
      HasDerivWithinAt (fun s => w s z) (velocity t z) (Icc a b) t := by
    intro t ht z hz
    exact ((hasDerivWithinAt_sectionalRayleighVelocity F t (hJ ht) z.1 z.2.1 z.2.2
      (hgram t z hz)).mono hJ).sub (hderiv t ht z.1 hz.1)
  have hm : ∀ t ∈ Ioc a b, ∀ z ∈ S,
      (∀ y ∈ S, w t z ≤ w t y) → w t z < 0 → -(0 : ℝ) * w t z ≤ velocity t z := by
    intro t ht z hz hmin hneg
    have htJ : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have hxint : z.1 ∈ interior K := by
      by_contra hn
      have hbnd := hboundary t htJ z.1 ⟨hz.1, hn⟩
      have hnon := hq0 t htJ z hz
      dsimp only [w] at hneg
      linarith
    let f := fun y : E => w t z + B t y
    have hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f := contMDiff_const.add (hsmooth t htJ)
    have hminf : ∀ y ∈ interior K, ∀ u v : TangentSpace (𝓡 3) y,
        f y * metricGram (F.metric t) y u v ≤
          (F.connection t).curvatureTensor y u v u v := by
      intro y hy u v
      apply sectional_lower_of_model_pairs (F.connection t) y (f y)
      intro p hp
      have h := hmin (y, p) ⟨interior_subset hy, hp⟩
      change w t z ≤ q t (y, p) - B t y at h
      change w t z + B t y ≤ q t (y, p)
      linarith
    have hfx : f z.1 = q t z := by dsimp only [f, w]; ring
    have hnull : (F.connection t).curvatureTensor z.1 z.2.1 z.2.2 z.2.1 z.2.2 =
        f z.1 * metricGram (F.metric t) z.1 z.2.1 z.2.2 := by
      rw [hfx]
      exact (div_mul_cancel₀ _ (hgram t z hz).ne').symm
    have hv := sectionalRayleighVelocity_ge_barrier (F.connection t) hf isOpen_interior
      hxint hminf z.2.1 z.2.2 (hgram t z hz) hnull
    have htrace := six_mul_sectional_lower_le_scalar (F.connection t) z.1 (f z.1)
      (hminf z.1 hxint)
    rw [hfx] at htrace hv
    have hreact : 0 ≤ q t z * ((F.connection t).scalarCurvature z.1 - 2 * q t z) :=
      mul_nonneg (hq0 t htJ z hz) (by linarith [hq0 t htJ z hz])
    have hlapf : (F.connection t).laplacian f z.1 =
        (F.connection t).laplacian (B t) z.1 := by
      dsimp only [f]
      rw [(F.connection t).laplacian_add contMDiff_const (hsmooth t htJ),
        M10.laplacian_const_scalar, zero_add]
    rw [hlapf] at hv
    have hbheat := hevol t ht z.1 hxint
    dsimp only [velocity]
    linarith
  have hi (z : E × (E × E)) (hz : z ∈ S) : 0 ≤ w a z :=
    sub_nonneg.mpr (hinit z.1 hz.1 z.2 hz.2)
  have hresult := compact_subset_min_velocity_nonnegative_Icc
    (hK.prod (isCompact_modelOrthonormalPairs 3)) (K := 0) hab w velocity hw hd hm hi
  exact fun t ht x hx p hp => sub_nonneg.mp (hresult t ht (x, p) ⟨hx, hp⟩)

end PoincareConjecture.M34
