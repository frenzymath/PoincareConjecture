import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteAnnulusChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularArcGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularTraceChart






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






theorem annulus_regular_boundary_gradient (A : M64Annulus g c0 c1)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 curvePeriod) (upper : Bool)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {c : ℝ → M} {sigma : ℝ → ℝ} (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ c)
    (hcv : ∀ s, curveVelocity (n := n) c s ≠ 0) (hsigma : ContDiff ℝ 1 sigma)
    (htrace : ∀ s, A.map (annulusPoint s (if upper then 1 else 0)) = c (sigma s)) :
    let a := annulusPoint x (if upper then 1 else 0)
    let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
    let P := annulusBoundarySource r hr.ne' upper x
    let H := q ∘ A.map ∘ P
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
      (R d : ℝ), 0 < R ∧ R < 1 ∧ r * R < x ∧ x + r * R < curvePeriod ∧ 0 < d ∧ d < R ∧
      let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
      let Kd := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
      let Wd := ball (0 : ℂ) d ∩ {z | 0 < z.im}
      MapsTo (A.map ∘ P) K q.source ∧ ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm) ∧
      (∀ z ∈ K, let T := fderivWithin ℝ H K z
        gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
          gE.inner (H z) (T 1) (T I) = 0) ∧
      (∀ z ∈ W, dbar (complexGradient H) z = harmonicMatrix DE H z (complexGradient H z)) ∧
      (∀ z ∈ K, Function.Injective (fderivWithin ℝ H K z)) ∧
      ContDiffOn ℝ 1 (complexGradient H) Wd ∧
      MemLp (fun z => fderiv ℝ (complexGradient H) z 1) 2 (volume.restrict Wd) ∧
      MemLp (fun z => fderiv ℝ (complexGradient H) z I) 2 (volume.restrict Wd) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Kd, ∀ w ∈ Kd,
        ‖halfDiskGradient H R z - halfDiskGradient H R w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  let a := annulusPoint x (if upper then 1 else 0)
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
  let P := annulusBoundarySource r hr.ne' upper x
  let H := q ∘ A.map ∘ P
  obtain ⟨gE, DE, R, hR, hR1, hRx, hRP, hsrc, hH, hHi, hmetric, hconf, heq, hHinj⟩ :=
    annulus_boundary_coordinate_data A hr hx upper hminimum hAc hAi hconformal hinj
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im} := by simp [hR.le]
  have hsrc0 : c (sigma x) ∈ q.source := by
    rw [← htrace x]
    exact mem_chart_source _ _
  obtain ⟨hI, hsI, hcq, hcvq⟩ := regular_trace_in_chart hc (A.map a) hsrc0 (hcv (sigma x))
  let label := fun s : ℝ => sigma (x + r * s)
  have hlabel : ContDiff ℝ 1 label :=
    hsigma.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hlabel0 : label 0 = sigma x := by simp [label]
  have hzero : fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) 0 ≠ 0 := by
    intro hz
    have he : (1 : ℂ) = 0 := (hHinj 0 h0) (by rw [hz]; rfl)
    exact one_ne_zero he
  have hb (s : ℝ) (_hs : ‖(s : ℂ)‖ ≤ R) : H (s : ℂ) = (q ∘ c) (label s) := by
    simp only [H, P, Function.comp_apply, annulusBoundarySource_real, htrace, label]
  obtain ⟨d, hd, hdR, hgi, hg1, hgI, hholder⟩ :=
    halfDisk_regular_arc_gradient DE hR hI hcq hlabel
      (hlabel0.symm ▸ hsI) (hlabel0.symm ▸ hcvq) hH hHi hb hconf heq hzero
  exact ⟨gE, DE, R, d, hR, hR1, hRx, hRP, hd, hdR,
    hsrc, hH, hHi, hmetric, hconf, heq, hHinj, hgi, hg1, hgI, hholder⟩

end PoincareConjecture.M64
