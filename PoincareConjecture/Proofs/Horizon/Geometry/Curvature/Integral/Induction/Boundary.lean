import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.RegularLevels
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SectionalIntegral








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [IsManifold (𝓡 (m + 2)) ∞ M]
  {g : RiemannianMetric (m + 2) M}



theorem integral_scalarCurvature_posPart_le_regularLevels_area
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b α βa βb : ℝ} (hab : a < b) (hslab : Icc a b ⊆ I)
    (hα : 0 < α) (hβa : 0 ≤ βa) (hβb : 0 ≤ βb)
    {K : M → ℝ} (hKc : ContinuousOn K (f ⁻¹' Icc a b))
    (hK : ∀ x ∈ f ⁻¹' Icc a b, 0 ≤ K x)
    (hsec : ∀ x ∈ f ⁻¹' Icc a b, ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -K x ≤ D.sectionalCurvature x v w)
    (hha : ∀ x, f x = a → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ βa * g.inner x v v)
    (hhb : ∀ x, f x = b → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ βb * g.inner x v v)
    (hspeed : ∀ x, f x = b →
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI (c : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) c
    letI (c : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) c
    let DL := fun c => (RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) c g).leviCivitaData
    (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      2 * (∫ c in Icc a b, ∫ z,
        max 0 ((DL c).scalarCurvature z) /
          g.tangentNorm (openLevelIncl f U c z)
            (g.gradient f (openLevelIncl f U c z))
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) c) +
      2 * ((m + 2 : ℕ) : ℝ) ^ 2 * (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
      2 * ((m + 1 : ℕ) : ℝ) * βa * g.regularLevelArea hf a +
      2 * ((m + 1 : ℕ) : ℝ) * α * βb * g.regularLevelArea hf b -
      2 * deriv (g.regularLevelArea hf) b := by
  have ha : a ∈ I := hslab ⟨le_rfl, hab.le⟩
  have hb : b ∈ I := hslab ⟨hab.le, le_rfl⟩
  have hc := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hslab
  have hregular : ∀ x ∈ f ⁻¹' Icc a b,
      mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx => hreg x (hslab hx)
  have hq {x : M} (hx : f x ∈ I) : 0 < D.levelQ f x :=
    Real.sqrt_pos.mp ((g.tangentNorm_gradient_pos_iff f x).mpr (hreg x hx))
  have hHa : ∀ x, f x = a → D.levelMeanCurvature f x ≤ ((m + 1 : ℕ) : ℝ) * βa := by
    intro x hx
    exact D.levelMeanCurvature_le_of_tangentialHessian (hq (by rwa [hx])) βa (hha x hx)
  have hHb : ∀ x, f x = b → D.levelMeanCurvature f x ≤ ((m + 1 : ℕ) : ℝ) * βb := by
    intro x hx
    exact D.levelMeanCurvature_le_of_tangentialHessian (hq (by rwa [hx])) βb (hhb x hx)
  let U := g.regularDomain hf
  let μ := fun t => g.regularLevelVolume hf U (g.regularDomain_regular hf) t
  let H := fun t z => D.levelMeanCurvature f (openLevelIncl f U t z)
  have hHi {t : ℝ} (ht : t ∈ I) :=
    integrable_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg ht
      (D.continuousOn_levelMeanCurvature_regularDomain hf)
  have hPa :=
    integrable_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg ha
      ((continuousOn_const (c := (0 : ℝ))).sup
        (D.continuousOn_levelMeanCurvature_regularDomain hf))
  have hNb :=
    integrable_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg hb
      ((continuousOn_const (c := (0 : ℝ))).sup
        (D.continuousOn_levelMeanCurvature_regularDomain hf).neg)
  have hleft : (∫ z, H a z ∂μ a) ≤
      ((m + 1 : ℕ) : ℝ) * βa * g.regularLevelArea hf a :=
    (integral_mono (hHi ha) hPa (fun z => le_max_right _ _)).trans
      (D.integral_pos_levelMeanCurvature_le hf hI hproper hreg ha hβa hHa)
  have hright : -(∫ z, H b z ∂μ b) ≤
      ((m + 1 : ℕ) : ℝ) * α * βb * g.regularLevelArea hf b -
        deriv (g.regularLevelArea hf) b := by
    rw [← integral_neg]
    exact (integral_mono (hHi hb).neg hNb (fun z => le_max_right _ _)).trans
      (D.integral_neg_levelMeanCurvature_le_sub_deriv hf hI hproper hreg hb hα hβb
        hHb hspeed)
  have hbound := D.integral_scalarCurvature_posPart_le_regularLevels
    hf hab hc hregular hKc hK hsec
  dsimp only at hbound ⊢
  dsimp only [H, μ, U] at hleft hright
  linarith only [hbound, hleft, hright]

end PoincareConjecture.LeviCivitaData
