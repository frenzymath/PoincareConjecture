import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.CanonicalAnnulusColumns
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m64_canonical_annulus_of_columns
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {gamma beta : ℝ → M} (f : LoopPlane → M)
    (hf : ∀ p ∈ m64AnnulusDomain, ContMDiffAt (𝓡 2) (𝓡 n) 1 f p)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x : ℝ, f (annulusPoint x 0) = gamma x)
    (hupper : ∀ x : ℝ, f (annulusPoint x 1) = beta x)
    {B epsilon mu : ℝ} (hB : 0 ≤ B) (hepsilon : 0 ≤ epsilon)
    (hcol0 : ∀ p ∈ m64AnnulusDomain,
      (F.metric t).tangentNorm (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B)
    (hcol1 : ∀ p ∈ m64AnnulusDomain,
      (F.metric t).tangentNorm (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ epsilon)
    (hcirc : circumference ≤ curvePeriod)
    (hstrict : (B + 1) * epsilon * volume.real m64AnnulusDomain < mu) :
    ∃ A : M64Annulus (P.flow.metric t) (m63CanonicalRamp P gamma) (m63CanonicalRamp P beta),
      A.map = m64CanonicalAnnulusMap P f ∧ A.area < mu := by
  let Amap := m64CanonicalAnnulusMap P f
  have hregular : ∀ p ∈ m64AnnulusDomain,
      ContMDiffAt (𝓡 2) (𝓡 (n + 1)) 1 Amap p :=
    fun p hp => m64CanonicalAnnulusMap_contMDiffAt P (hf p hp)
  have hcontinuous : ContinuousOn Amap m64AnnulusDomain :=
    fun p hp => (hregular p hp).continuousAt.continuousWithinAt
  obtain ⟨L, hLip⟩ := m64Annulus_hLip_of_local (P.flow.metric t) hcontinuous
    (fun p hp => m64_lipschitzOn_nhds_of_contMDiffAt (P.flow.metric t) (hregular p hp))
  have hLip' : ∀ x y : m64AnnulusDomain,
      (P.flow.metric t).edist (Amap x) (Amap y) ≤
        ENNReal.ofReal (L : ℝ) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hLip
  have hcolumns : ∀ p ∈ m64AnnulusDomain,
      (P.flow.metric t).tangentNorm (Amap p)
          (mfderiv (𝓡 2) (𝓡 (n + 1)) Amap p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B + 1 ∧
      (P.flow.metric t).tangentNorm (Amap p)
          (mfderiv (𝓡 2) (𝓡 (n + 1)) Amap p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ epsilon :=
    fun p hp => m64CanonicalAnnulusMap_column_bounds P t
      ((hf p hp).mdifferentiableAt one_ne_zero) hB hepsilon (hcol0 p hp) (hcol1 p hp) hcirc
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  have h0 : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      (P.flow.metric t).tangentNorm (Amap p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) Amap p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B + 1 := by
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp
    exact (hcolumns p hp).1
  have h1 : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      (P.flow.metric t).tangentNorm (Amap p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) Amap p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ epsilon := by
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp
    exact (hcolumns p hp).2
  have harea := m64AnnulusIntegral_le_of_lipschitzOn_and_ae_column_bounds
    (P.flow.metric t) L.coe_nonneg (show 0 ≤ B + 1 by linarith) hLip' hfinite h0 h1
  apply m64Annulus_of_lipschitz (P.flow.metric t) Amap hcontinuous
    ?_ ?_ ?_ L.coe_nonneg hLip' hfinite (harea.trans_lt hstrict)
  · intro x s
    have h := M63.canonicalRamp_periodic P
      (show Function.Periodic (fun y => f (annulusPoint y s)) curvePeriod from
        fun y => hperiodic y s) x
    exact h
  · intro x
    apply Prod.ext
    · exact hlower x
    · rfl
  · intro x
    apply Prod.ext
    · exact hupper x
    · rfl

end PoincareConjecture
