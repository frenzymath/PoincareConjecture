import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.StripLogDensity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.TruncatedCurvatureLimit

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

theorem annulus_truncated_gram_curvature_le
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {lo hi K : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) (hhi : hi < 1) (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    -(1 / 2 : ℝ) * r⁻¹ *
      ((∫ x in (0 : ℝ)..curvePeriod,
        fderiv ℝ (fun q => Real.log (m60AreaGram g A.map q 0 0))
          (annulusPoint x hi) (EuclideanSpace.single (1 : Fin 2) 1)) -
        ∫ x in (0 : ℝ)..curvePeriod,
          fderiv ℝ (fun q => Real.log (m60AreaGram g A.map q 0 0))
            (annulusPoint x lo) (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K * A.area := by
  have hpos (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
      0 < m64ModulusEnergyDensity g r A.map (annulusPoint x s) := by
    rw [annulus_strip_energy_eq A r hAc hAi hconformal hs]
    exact mul_pos hr (annulus_strip_gram_pos A hAc hinj hs)
  have hbound := annulus_truncated_log_curvature_le D A hr hminimum hconformal hAi
    hlo hlh hhi hK hsec (fun x _ => hpos lo ⟨hlo, hlh.trans_lt hhi⟩ x)
      (fun x _ => hpos hi ⟨hlo.trans_le hlh, hhi⟩ x)
  have heq (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      (∫ x in (0 : ℝ)..curvePeriod,
        fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q))
          (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1)) =
      ∫ x in (0 : ℝ)..curvePeriod,
        fderiv ℝ (fun q => Real.log (m60AreaGram g A.map q 0 0))
          (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact annulus_strip_log_energy A hr hAc hAi hconformal hinj hs _
  rwa [heq hi ⟨hlo.trans_le hlh, hhi⟩, heq lo ⟨hlo, hlh.trans_lt hhi⟩] at hbound

end PoincareConjecture.M64
