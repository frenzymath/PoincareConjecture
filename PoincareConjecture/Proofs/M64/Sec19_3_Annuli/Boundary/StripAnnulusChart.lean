import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.StripSourceNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ClosedStripDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusStripHarmonic
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteChartDifferential

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

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

set_option maxHeartbeats 1200000 in

theorem annulus_strip_boundary_coordinate_data (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (x : ℝ) (upper : Bool)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
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
      (R : ℝ), 0 < R ∧ R < 1 ∧
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
  have ha : a ∈ S := by cases upper <;> norm_num [a, annulusPoint, Set.mem_ofPred_eq]
  have hWS : m64AnnulusOpenStrip ⊆ S := fun _ hp => ⟨hp.1.le, hp.2.le⟩
  have hIW : m64AnnulusInterior ⊆ m64AnnulusOpenStrip :=
    fun p hp => ((mem_m64AnnulusInterior_iff p).mp hp).2.2
  obtain ⟨gE, DE, O, hO, haO, hAO, hHc, hHi, hgerm⟩ :=
    exists_finite_target_chart g hWS hAc hAi ha
  obtain ⟨R, hR, hR1, hPO⟩ := annulusBoundarySource_strip_radius r x hr.ne' upper hO haO
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
  have hKS := annulusBoundarySource_mapsTo_closedStrip r x hr.ne' hR1 upper
  have hWW := annulusBoundarySource_mapsTo_openStrip r x hr.ne' hR1 upper
  have hWK : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hKSO : MapsTo P K (S ∩ O) := fun z hz => ⟨hKS hz, hPO hz⟩
  have hWWO : MapsTo P W (m64AnnulusOpenStrip ∩ O) :=
    fun z hz => ⟨hWW hz, hPO (hWK hz)⟩
  have hP : ContDiff ℝ ∞ P := contDiff_const.add e.contDiff
  have hsource : MapsTo (A.map ∘ P) K q.source := fun z hz => hAO (hKSO hz)
  have hmetric (z : ℂ) (hz : z ∈ K) :
      gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm := hgerm _ (hKSO hz)
  have hUD := (halfDisk_differential_domain hR).2.2.1
  have hfull := annulus_strip_within_conformal A r hAc (hAi.mono hIW) hconformal
  have hSInj := annulus_strip_within_injective A hAc hinj
  have hder (z : ℂ) (hz : z ∈ K) :
      fderivWithin ℝ H K z = (mfderiv (𝓡 n) (𝓡 n) q (A.map (P z))).comp
        ((mfderivWithin (𝓡 2) (𝓡 n) A.map S (P z)).comp e.toContinuousLinearMap) :=
    within_chart_affine_derivative (A.map a) e a
      ((hAc _ (hKS hz)).mdifferentiableWithinAt one_ne_zero) (hUD _ hz) hKS (hsource hz)
  have hpair (z : ℂ) (hz : z ∈ K) (v w : ℂ) :
      gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z w) =
        g.inner (A.map (P z))
          (mfderivWithin (𝓡 2) (𝓡 n) A.map S (P z) (e v))
          (mfderivWithin (𝓡 2) (𝓡 n) A.map S (P z) (e w)) :=
    within_chart_affine_metric g (A.map a) e a
      ((hAc _ (hKS hz)).mdifferentiableWithinAt one_ne_zero) (hUD _ hz) hKS (hsource hz)
      (hmetric z hz).self_of_nhds v w
  refine ⟨gE, DE, R, hR, hR1, hsource,
    hHc.comp (hP.of_le (by simp)).contDiffOn hKSO,
    hHi.comp hP.contDiffOn hWWO, hmetric, ?_, ?_, ?_⟩
  · intro z hz
    dsimp only
    rw [hpair z hz, hpair z hz, hpair z hz]
    have hc := hfull (P z) (hKS hz)
    dsimp only at hc
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
    have hU : IsOpen (m64AnnulusOpenStrip ∩ O) := isOpen_m64AnnulusOpenStrip.inter hO
    have heq := annulus_chart_harmonic_on_strip A hr hminimum hconformal hAi
      (A.map a) (P z) (hWW hz)
      (by simpa only [extChartAt_source, q, Function.comp_apply] using hsource (hWK hz))
    apply modulus_harmonic_equation_comp_affine (u := q ∘ A.map)
      (B := g.pullbackCoefficients q.symm) DE hr e a z
      (annulusBoundaryLinear_one r hr.ne' upper)
    · cases upper
      · exact Or.inl (annulusBoundaryLinear_I r hr.ne' false)
      · exact Or.inr (annulusBoundaryLinear_I r hr.ne' true)
    · exact hHi.contDiffAt (hU.mem_nhds (hWWO hz))
    · exact hmetric z (hWK hz)
    · simpa +instances only [annulusWeightedTension, extChartAt_coe, extChartAt_coe_symm,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
        Function.comp_id, q, P, annulusBoundarySource, e, a] using! heq
  · intro z hz
    rw [hder z hz]
    exact ((mdifferentiable_chart (I := 𝓡 n) (A.map a)).mfderiv (hsource hz)).injective.comp
      ((hSInj (P z) (hKS hz)).comp e.injective)

end PoincareConjecture.M64
