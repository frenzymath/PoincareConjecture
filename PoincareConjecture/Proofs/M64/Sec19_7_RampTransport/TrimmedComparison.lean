import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.TrimmedGaussianBound
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.TrimmedPolarArea
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.InducedBoundaryGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.TrimmedBoundaryApproximation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_BoundaryNormal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

private theorem boundary_mem_standard {radius : ℝ} (hr : radius ∈ Icc (1 : ℝ) 2)
    (x : ℝ) : intrinsicAnnulusBoundary radius x ∈ standardAnnulusDomain := by
  have hsq := m64Intrinsic_boundary_self_inner radius x
  rw [real_inner_self_eq_norm_sq] at hsq
  have hn : ‖intrinsicAnnulusBoundary radius x‖ = radius := by
    nlinarith [norm_nonneg (intrinsicAnnulusBoundary radius x), hr.1]
  change 1 ≤ ‖intrinsicAnnulusBoundary radius x‖ ∧
    ‖intrinsicAnnulusBoundary radius x‖ ≤ 2
  rw [hn]
  exact ⟨hr.1, hr.2⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (time : ℝ)
  {c0 c1 : ℝ → M}

theorem m64_trimmed_boundary_comparison
    (A : M64Annulus (F.metric time) c0 c1)
    {modulus : ℝ} (hm : 0 < modulus)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric time) c0 c1)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      modulus * m60AreaGram (F.metric time) A.map p 0 0 =
        modulus⁻¹ * m60AreaGram (F.metric time) A.map p 1 1 ∧
        m60AreaGram (F.metric time) A.map p 0 1 = 0)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {r eta width K mu : ℝ}
    (T : M64.RampTransport.TrimmedBoundaryControl F time A.map r eta width)
    (hsec : ∀ p u v, (F.connection time).sectionalCurvature p u v ≤ K)
    (hcomparison : ∀ N : IntrinsicAnnulus,
      N.GaussianCurvatureBound K →
      r / 4 < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
      N.SmallBoundaryTurning (7 / 800) (r / 4) →
      intrinsicAnnulusArea N.metric < mu →
        (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod ≤
          intrinsicBoundaryLength N.metric 2 0 rampPeriod)
    (harea : A.area < mu) :
    (3 / 4 : ℝ) * m62Length F (fun y _ => A.map (annulusPoint y width)) time ≤
      m62Length F (fun y _ => A.map (annulusPoint y (1 - width))) time := by
  obtain ⟨N, j, hdesc, hj, _hinj, hmetric, hlo, hhi⟩ :=
    m64Annulus_exists_trimmed_intrinsic_metric A hAc hAi hinj T.width_pos T.width_lt_half
  have hGaussian := m64Annulus_trimmed_gaussian_bound (F.connection time) A hm
    hminimum hconf hAc hAi hinj T.width_pos T.width_lt_half N hdesc hmetric hsec
  have hArea := m64TrimmedPolarDescent_intrinsic_area_le A T.width_pos T.width_lt_half
    hdesc N.metric (fun p hp => (hmetric p hp).self_of_nhds)
  have hjnear {radius : ℝ} (hradius : radius ∈ Icc (1 : ℝ) 2) (x : ℝ) :
      ∀ᶠ q in 𝓝 (intrinsicAnnulusBoundary radius x), ContMDiffAt (𝓡 2) (𝓡 n) ∞ j q := by
    have hx := standardAnnulusDomain_subset_trimmedNeighborhood T.width_pos T.width_lt_half
      (boundary_mem_standard hradius x)
    filter_upwards [(isOpen_m64TrimmedAnnulusNeighborhood width).mem_nhds hx] with q hq
    exact hj.contMDiffAt ((isOpen_m64TrimmedAnnulusNeighborhood width).mem_nhds hq)
  have hmnear {radius : ℝ} (hradius : radius ∈ Icc (1 : ℝ) 2) (x : ℝ) :=
    hmetric _ (boundary_mem_standard hradius x)
  have h1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have h2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have hlen0 (alpha beta : ℝ) : intrinsicBoundaryLength N.metric 1 alpha beta =
      m63ArcLength F (fun y _ => A.map (annulusPoint y width)) time alpha beta := by
    simpa only [m63ArcLength, hlo] using m64_induced_boundary_length F time N
      (fun x => (hjnear h1 x).self_of_nhds.mdifferentiableAt (by simp))
      (fun x => (hmnear h1 x).self_of_nhds) alpha beta
  have hlen1 : intrinsicBoundaryLength N.metric 2 0 rampPeriod =
      m62Length F (fun y _ => A.map (annulusPoint y (1 - width))) time := by
    simpa only [hhi, curvePeriod, rampPeriod] using m64_induced_boundary_m62Length F time N
      (fun x => (hjnear h2 x).self_of_nhds.mdifferentiableAt (by simp))
      (fun x => (hmnear h2 x).self_of_nhds)
  have hturn : N.SmallBoundaryTurning (7 / 800) (r / 4) := by
    intro alpha beta hab hp hlength
    have ht := m64_induced_boundary_turning_integral_le F time N (by norm_num : (1 : ℝ) ≠ 0)
      (hjnear h1) (hmnear h1) hab
    have ht' : intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 alpha beta ≤
        m63ArcTotalCurvature F (fun y _ => A.map (annulusPoint y width)) time alpha beta := by
      simpa only [m63ArcTotalCurvature, hlo] using ht
    exact ht'.trans_lt (T.lower_turning alpha beta hab hp ((hlen0 alpha beta) ▸ hlength))
  have hfirst : r / 4 < intrinsicBoundaryLength N.metric 1 0 rampPeriod := by
    rw [hlen0]
    exact T.lower_length_strict
  have h := hcomparison N hGaussian hfirst hturn (hArea.trans_lt harea)
  rw [hlen0, hlen1] at h
  exact h

end PoincareConjecture
