import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapHarmonicChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.StripAnnulusChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularTraceChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularArcGradient












set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Complex
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64.RampTransport

open M65Branch M65StrictTrace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M} {c0 c1 : ℝ → M}






theorem annulus_strip_boundary_coordinate_c2 (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (x : ℝ) (upper : Bool)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map
      {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hAi : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 (n + 1)) A.map m64AnnulusDomain p))
    {c : ℝ → M} {sigma : ℝ → ℝ}
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ c)
    (hcv : ∀ s, curveVelocity (n := n + 1) c s ≠ 0) (hsigma : ContDiff ℝ 1 sigma)
    (htrace : ∀ s, A.map (annulusPoint s (if upper then 1 else 0)) = c (sigma s)) :
    let a := annulusPoint x (if upper then 1 else 0)
    let q := chartAt (EuclideanSpace ℝ (Fin (n + 1))) (A.map a)
    let P := annulusBoundarySource r hr.ne' upper x
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      MapsTo (A.map ∘ P) (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) q.source ∧
      ContDiffOn ℝ 2 (q ∘ A.map ∘ P) (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) := by
  let a := annulusPoint x (if upper then 1 else 0)
  let q := chartAt (EuclideanSpace ℝ (Fin (n + 1))) (A.map a)
  let P := annulusBoundarySource r hr.ne' upper x
  let H := q ∘ A.map ∘ P
  obtain ⟨gE, DE, R, hR, hR1, hsrc, hH, hHs, _, hconf, heq, hHinj⟩ :=
    annulus_strip_boundary_coordinate_data A hr x upper hminimum hAc hAi hconformal hinj
  have hsrc0 : c (sigma x) ∈ q.source := by
    rw [← htrace x]
    exact mem_chart_source _ _
  obtain ⟨hJ, hsJ, hcq, hcvq⟩ := regular_trace_in_chart hc (A.map a) hsrc0 (hcv (sigma x))
  let label := fun s : ℝ => sigma (x + r * s)
  have hlabel : ContDiff ℝ 1 label :=
    hsigma.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hlabel0 : label 0 = sigma x := by simp [label]
  have htraceQ (s : ℝ) : H (s : ℂ) = (q ∘ c) (label s) := by
    simp only [H, P, Function.comp_apply, annulusBoundarySource_real, htrace, label]
  have h0K : (0 : ℂ) ∈ closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im} := by simp [hR.le]
  have hzero : fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) 0 ≠ 0 := by
    intro hz
    have he : (1 : ℂ) = 0 := (hHinj 0 h0K) (by rw [hz]; rfl)
    exact one_ne_zero he
  obtain ⟨d, hd, hdR, _, hG1, hGI, _⟩ :=
    halfDisk_regular_arc_gradient DE hR hJ hcq hlabel
      (hlabel0.symm ▸ hsJ) (hlabel0.symm ▸ hcvq) hH hHs
      (fun s _ => htraceQ s) hconf heq hzero
  have hKsub : closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im} ⊆
      closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im} :=
    fun _ hz => ⟨closedBall_subset_closedBall hdR.le hz.1, hz.2⟩
  have hWsub : ball (0 : ℂ) d ∩ {z | 0 < z.im} ⊆
      ball (0 : ℂ) R ∩ {z | 0 < z.im} :=
    fun _ hz => ⟨ball_subset_ball hdR.le hz.1, hz.2⟩
  have hder (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) :
      fderivWithin ℝ H (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) z =
        fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) z :=
    fderivWithin_subset hKsub ((halfDisk_differential_domain hd).2.2.1 z hz)
      ((hH z (hKsub hz)).differentiableWithinAt one_ne_zero)
  have hdiam (s : ℝ) (hs : |s| ≤ d) :
      (s : ℂ) ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im} := by
    exact ⟨mem_closedBall_zero_iff.mpr (by simpa only [norm_real, Real.norm_eq_abs] using hs),
      by simp⟩
  have hcqreg (t : ℝ) (ht : t ∈ c ⁻¹' q.source) : deriv (q ∘ c) t ≠ 0 :=
    (regular_trace_in_chart hc (A.map a) ht (hcv t)).2.2.2
  obtain ⟨e, he, hed, hC2⟩ := harmonic_regular_trace_exists_closed_c2 DE hd
    (hH.mono hKsub) (hHs.mono hWsub) hG1 hGI (fun z hz => heq z (hWsub hz))
    hJ hcq hcqreg hlabel (hlabel0.symm ▸ hsJ) (fun s _ => htraceQ s)
    (fun s hs => by rw [hder _ (hdiam s hs)]; exact hHinj _ (hKsub (hdiam s hs)))
    (fun s hs => by rw [hder _ (hdiam s hs)]; exact (hconf _ (hKsub (hdiam s hs))).2)
  refine ⟨e, he, hed.trans (hdR.trans hR1), ?_, hC2⟩
  intro z hz
  exact hsrc ⟨closedBall_subset_closedBall (hed.trans hdR).le hz.1, hz.2⟩

end PoincareConjecture.M64.RampTransport
