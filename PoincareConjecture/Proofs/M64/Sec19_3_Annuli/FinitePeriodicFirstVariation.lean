import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteAnnulusFirstVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteCurrentPeriodicity





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {d : ℕ} {c0 c1 : ℝ → M}





theorem m64ParameterAnnulus_periodic_first_variation
    (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (A : M64Annulus (F.metric t) c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
      m60AreaGram (F.metric t) A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map
      {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1})
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hTF : ∀ s ∈ Ioo (-epsilon) epsilon, t + s ∈ Ioo a b)
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O)
    {Phi : ℝ × EuclideanSpace ℝ (Fin d) → M}
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 d)) (𝓡 n) ∞ Phi
      (Ioo (-epsilon) epsilon ×ˢ O))
    {h : LoopPlane → EuclideanSpace ℝ (Fin d)}
    (hh : ContDiffOn ℝ 1 h m64AnnulusDomain) (hmap : MapsTo h m64AnnulusDomain O)
    (hbase : ∀ p, Phi (0, h p) = A.map p)
    (hperiodic : ∀ s x y, Phi (s, h (annulusPoint (x + curvePeriod) y)) =
      Phi (s, h (annulusPoint x y))) :
    let v := fun s p => Phi (s, h p)
    let R := fun p =>
      r * (F.connection t).ricci (v 0 p)
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      r⁻¹ * (F.connection t).ricci (v 0 p)
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
        m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p)
      (r⁻¹ * (∫ x in Icc (0 : ℝ) curvePeriod,
        m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 1) -
          m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 0)) -
        ∫ p in m64AnnulusDomain, R p) 0 := by
  let v := fun s p => Phi (s, h p)
  let J := m64FiniteAnnulusCurrent (F.metric t) v
  have hPhi' : ContMDiffOn 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin d)) (𝓡 n) ∞ Phi
      (Ioo (-epsilon) epsilon ×ˢ O) := by
    simpa +instances only [modelWithCornersSelf_prod, chartedSpaceSelf_prod] using! hPhi
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hv0 : ContMDiffOn (𝓡 2) (𝓡 n) 1 (v 0) m64AnnulusDomain :=
    (hPhi.of_le (by simp)).comp (contMDiffOn_const.prodMk hh.contMDiffOn)
      (fun _ hp => ⟨hzero, hmap hp⟩)
  have hV := m64ParameterAnnulus_timeVelocity_contMDiffOn isOpen_Ioo hO hPhi' hh hmap hzero
  have hc (i : Fin 2) : ContinuousOn (J i) m64AnnulusDomain :=
    m64FiniteAnnulusCurrent_continuousOn (F.metric t) hv0 hV.continuousOn i
  have hseam := m64FiniteAnnulusCurrent_seam A hbase hperiodic hc hA 0
  have hcuts : (∫ y in Icc (0 : ℝ) 1, r * J 0 (annulusPoint curvePeriod y)) =
      ∫ y in Icc (0 : ℝ) 1, r * J 0 (annulusPoint 0 y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact congrArg (fun z : ℝ => r * z) (hseam y hy)
  have htrace (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun x => J 1 (annulusPoint x y)) (Icc (0 : ℝ) curvePeriod) volume := by
    have hline : Continuous (fun x : ℝ => annulusPoint x y) := by
      unfold annulusPoint
      fun_prop
    exact ((hc 1).comp hline.continuousOn
      (fun _ hx => ⟨hx.1, hx.2, hy.1, hy.2⟩)).integrableOn_compact isCompact_Icc
  have hinside : m64AnnulusInterior ⊆ {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} := by
    intro p hp
    exact hp 1 (mem_univ _)
  have hd := m64ParameterAnnulus_boundary_first_variation F ht A hr hminimum hconformal
    (hA.mono hinside) hepsilon hTF hO hPhi' hh hmap hbase
  apply hd.congr_deriv
  dsimp only
  change ((∫ x in Icc (0 : ℝ) curvePeriod, r⁻¹ * J 1 (annulusPoint x 1)) -
      (∫ x in Icc (0 : ℝ) curvePeriod, r⁻¹ * J 1 (annulusPoint x 0))) +
      ((∫ y in Icc (0 : ℝ) 1, r * J 0 (annulusPoint curvePeriod y)) -
        ∫ y in Icc (0 : ℝ) 1, r * J 0 (annulusPoint 0 y)) - _ = _
  rw [hcuts, sub_self, add_zero, integral_const_mul, integral_const_mul,
    integral_sub (htrace 1 (by simp)) (htrace 0 (by simp)), mul_sub]

end PoincareConjecture
