import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCurvatureConormal
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusMinimalBoundaryCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {c0 c1 : ℝ → M}

theorem m64Annulus_boundary_curvature_flux_le_of_conformal_minimum
    (F : RicciFlow n M (Icc a b)) {t : ℝ}
    (A : M64Annulus (F.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (F.metric t) A.map p 0 0 = m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, (F.connection t).sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity (F.metric t) A.map (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity (F.metric t) A.map (annulusPoint x 1)) :
    (∫ x in Icc (0 : ℝ) curvePeriod,
      (F.metric t).inner (A.map (annulusPoint x 1))
        (m62CurvatureVector F (fun y _ => A.map (annulusPoint y 1)) t x)
        (curveVelocity (fun r => A.map (annulusPoint x r)) 1) -
      (F.metric t).inner (A.map (annulusPoint x 0))
        (m62CurvatureVector F (fun y _ => A.map (annulusPoint y 0)) t x)
        (curveVelocity (fun r => A.map (annulusPoint x r)) 0)) ≤ K * A.area := by
  let E := m60EnergyDensity (F.metric t) A.map
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let R := fun s x => fderiv ℝ E (annulusPoint x s) e1 / E (annulusPoint x s)
  have hE : ContDiffOn ℝ ∞ E O := m64EnergyDensity_contDiffOn hO hA
  have hD : ContinuousOn (fun p => fderiv ℝ E p e1) O :=
    ((hE.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hpoint {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod)
      (hs : s ∈ Icc (0 : ℝ) 1) : annulusPoint x s ∈ m64AnnulusDomain := by
    change 0 ≤ x ∧ x ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
    exact ⟨hx.1, hx.2, hs⟩
  have hratio (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (hpos : ∀ x ∈ Icc (0 : ℝ) curvePeriod, 0 < E (annulusPoint x s)) :
      IntegrableOn (R s) (Icc (0 : ℝ) curvePeriod) volume := by
    have hline : Continuous (fun x => annulusPoint x s) := by
      unfold annulusPoint
      fun_prop
    have hmap : MapsTo (fun x => annulusPoint x s) (Icc (0 : ℝ) curvePeriod) O :=
      fun _ hx => hdom (hpoint hx hs)
    exact ((hD.comp hline.continuousOn hmap).div
      (hE.continuousOn.comp hline.continuousOn hmap)
      (fun x hx => (hpos x hx).ne')).integrableOn_compact isCompact_Icc
  have hi0 := hratio 0 (by simp) hlower
  have hi1 := hratio 1 (by simp) hupper
  have heq : (∫ x in Icc (0 : ℝ) curvePeriod,
      (F.metric t).inner (A.map (annulusPoint x 1))
        (m62CurvatureVector F (fun y _ => A.map (annulusPoint y 1)) t x)
        (curveVelocity (fun r => A.map (annulusPoint x r)) 1) -
      (F.metric t).inner (A.map (annulusPoint x 0))
        (m62CurvatureVector F (fun y _ => A.map (annulusPoint y 0)) t x)
        (curveVelocity (fun r => A.map (annulusPoint x r)) 0)) =
      -(1 / 2 : ℝ) * ((∫ x in Icc (0 : ℝ) curvePeriod, R 1 x) -
        ∫ x in Icc (0 : ℝ) curvePeriod, R 0 x) := by
    calc
      _ = ∫ x in Icc (0 : ℝ) curvePeriod,
          -(1 / 2 : ℝ) * R 1 x - (-(1 / 2 : ℝ) * R 0 x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        rw [m64Annulus_curvature_conormal_eq F A hO hdom hA hconformal
          (hpoint hx (by simp)) (hupper x hx),
          m64Annulus_curvature_conormal_eq F A hO hdom hA hconformal
          (hpoint hx (by simp)) (hlower x hx)]
      _ = _ := by
        rw [integral_sub (hi1.const_mul _) (hi0.const_mul _),
          integral_const_mul, integral_const_mul]
        ring
  rw [heq]
  exact m64Annulus_log_boundary_curvature_le_of_conformal_minimum
    (F.connection t) A hminimum hconformal hO hdom hA hK hsec hlower hupper

end PoincareConjecture
