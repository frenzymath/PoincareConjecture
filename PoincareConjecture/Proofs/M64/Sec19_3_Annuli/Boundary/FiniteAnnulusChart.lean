import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusSourceNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteChartDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteConformality
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimumHarmonic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory Complex
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

set_option maxHeartbeats 1200000 in

theorem annulus_boundary_coordinate_data (A : M64Annulus g c0 c1)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 curvePeriod) (upper : Bool)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p)) :
    let a := annulusPoint x (if upper then 1 else 0)
    let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
    let P := annulusBoundarySource r hr.ne' upper x
    let H := q ∘ A.map ∘ P
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
      (R : ℝ), 0 < R ∧ R < 1 ∧ r * R < x ∧ x + r * R < curvePeriod ∧
      let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
      MapsTo (A.map ∘ P) K q.source ∧ ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm) ∧
      (∀ z ∈ K, let T := fderivWithin ℝ H K z
        gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
          gE.inner (H z) (T 1) (T I) = 0) ∧
      (∀ z ∈ W, dbar (complexGradient H) z = harmonicMatrix DE H z (complexGradient H z)) ∧
      (∀ z ∈ K, Function.Injective (fderivWithin ℝ H K z)) := by
  let a := annulusPoint x (if upper then 1 else 0)
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
  let e := annulusBoundaryLinear r hr.ne' upper
  let P := annulusBoundarySource r hr.ne' upper x
  let H := q ∘ A.map ∘ P
  have ha : a ∈ m64AnnulusDomain := by
    cases upper <;> exact ⟨hx.1.le, hx.2.le, by norm_num [a, annulusPoint],
      by norm_num [a, annulusPoint]⟩
  have hID : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  obtain ⟨gE, DE, O, hO, haO, hAO, hHc, hHi, hgerm⟩ :=
    exists_finite_target_chart g hID hAc hAi ha
  obtain ⟨R, hR, hR1, hRx, hRP, hPO⟩ := annulusBoundarySource_radius hr hx upper hO haO
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
  have hKD := annulusBoundarySource_mapsTo_closed hr hR1 hRx hRP upper
  have hWI := annulusBoundarySource_mapsTo_open hr hR1 hRx hRP upper
  have hWK : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hKDO : MapsTo P K (m64AnnulusDomain ∩ O) := fun z hz => ⟨hKD hz, hPO hz⟩
  have hWIO : MapsTo P W (m64AnnulusInterior ∩ O) :=
    fun z hz => ⟨hWI hz, hPO (hWK hz)⟩
  have hP : ContDiff ℝ ∞ P := contDiff_const.add e.contDiff
  have hsource : MapsTo (A.map ∘ P) K q.source := fun z hz => hAO (hKDO hz)
  have hmetric (z : ℂ) (hz : z ∈ K) :
      gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm := hgerm _ (hKDO hz)
  have hUD := (halfDisk_differential_domain hR).2.2.1
  have hfull := m64AnnulusWithinGram_modulus_conformal A r hAc hAi hconformal
  have hder (z : ℂ) (hz : z ∈ K) :
      fderivWithin ℝ H K z = (mfderiv (𝓡 n) (𝓡 n) q (A.map (P z))).comp
        ((mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain (P z)).comp e.toContinuousLinearMap) :=
    within_chart_affine_derivative (A.map a) e a
      ((hAc _ (hKD hz)).mdifferentiableWithinAt (by norm_num)) (hUD _ hz) hKD (hsource hz)
  have hpair (z : ℂ) (hz : z ∈ K) (v w : ℂ) :
      gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z w) =
        g.inner (A.map (P z))
          (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain (P z) (e v))
          (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain (P z) (e w)) :=
    within_chart_affine_metric g (A.map a) e a
      ((hAc _ (hKD hz)).mdifferentiableWithinAt (by norm_num)) (hUD _ hz) hKD (hsource hz)
      (hmetric z hz).self_of_nhds v w
  refine ⟨gE, DE, R, hR, hR1, hRx, hRP, hsource,
    hHc.comp (hP.of_le (by simp)).contDiffOn hKDO,
    hHi.comp hP.contDiffOn hWIO, hmetric, ?_, ?_, ?_⟩
  · intro z hz
    dsimp only
    rw [hpair z hz, hpair z hz, hpair z hz]
    have hc := hfull (P z) (hKD hz)
    change r * g.inner _ _ _ = r⁻¹ * g.inner _ _ _ ∧ g.inner _ _ _ = 0 at hc
    have he1 : e 1 = r • EuclideanSpace.basisFun (Fin 2) ℝ 0 :=
      annulusBoundaryLinear_one r hr.ne' upper
    have heI := annulusBoundaryLinear_I r hr.ne' upper
    change e I = _ at heI
    rw [he1, heI]
    have hdiag := congrArg (fun t : ℝ => r * t) hc.1
    simp only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hdiag
    cases upper <;> simp only [Bool.false_eq_true, if_false, if_true, map_smul,
      map_neg, smul_apply, neg_apply, smul_eq_mul, neg_neg]
    · exact ⟨by nlinarith [hdiag], by rw [hc.2, mul_zero]⟩
    · exact ⟨by nlinarith [hdiag], by rw [hc.2, mul_zero, neg_zero]⟩
  · intro z hz
    have hU : IsOpen (m64AnnulusInterior ∩ O) := isOpen_m64AnnulusInterior.inter hO
    have heq := m64Annulus_chart_harmonic_of_modulus_minimum A hr hminimum hconformal
      (A.map a) hU inter_subset_left (hAi.mono inter_subset_left)
      (fun y hy => by simpa only [extChartAt_source] using hAO ⟨hID hy.1, hy.2⟩)
      (P z) (hWIO hz)
    apply modulus_harmonic_equation_comp_affine (u := q ∘ A.map)
      (B := g.pullbackCoefficients q.symm) DE hr e a z
      (annulusBoundaryLinear_one r hr.ne' upper)
    · cases upper
      · exact Or.inl (annulusBoundaryLinear_I r hr.ne' false)
      · exact Or.inr (annulusBoundaryLinear_I r hr.ne' true)
    · exact hHi.contDiffAt (hU.mem_nhds (hWIO hz))
    · exact hmetric z (hWK hz)
    · simpa +instances only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
        q, P, annulusBoundarySource, e, a] using! heq
  · intro z hz
    rw [hder z hz]
    exact ((mdifferentiable_chart (I := 𝓡 n) (A.map a)).mfderiv (hsource hz)).injective.comp
      ((hinj (P z) (hKD hz)).comp e.injective)

end PoincareConjecture.M64
