import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.StripAnnulusChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularTraceChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularArcFrame

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

theorem annulus_regular_boundary_frame (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (x : ℝ) (upper : Bool)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {c : ℝ → M} {sigma : ℝ → ℝ} (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ c)
    (hcv : ∀ s, curveVelocity (n := n) c s ≠ 0) (hsigma : ContDiff ℝ 1 sigma)
    (hmono : Monotone sigma)
    (htrace : ∀ s, A.map (annulusPoint s (if upper then 1 else 0)) = c (sigma s)) :
    let a := annulusPoint x (if upper then 1 else 0)
    let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
    let P := annulusBoundarySource r hr.ne' upper x
    let H := q ∘ A.map ∘ P
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
      (R d : ℝ), 0 < R ∧ R < 1 ∧ 0 < d ∧ d < R ∧
      let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
      let Kd := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
      let Wd := ball (0 : ℂ) d ∩ {z | 0 < z.im}
      let V := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z))
        (halfDiskGradient H R z)
      MapsTo (A.map ∘ P) K q.source ∧ ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm) ∧
      (∀ z ∈ K, let T := fderivWithin ℝ H K z
        gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
          gE.inner (H z) (T 1) (T I) = 0) ∧
      (∀ z ∈ W, dbar (complexGradient H) z = harmonicMatrix DE H z (complexGradient H z)) ∧
      ContinuousOn V Kd ∧ ContDiffOn ℝ 1 V Wd ∧
      (∀ z ∈ Kd, gE.inner (H z) (V z).1 (V z).1 = 1 ∧
        gE.inner (H z) (V z).1 (V z).2 = 0 ∧ gE.inner (H z) (V z).2 (V z).2 = 1) ∧
      MemLp (fun z => fderiv ℝ V z 1) 2 (volume.restrict Wd) ∧
      MemLp (fun z => fderiv ℝ V z I) 2 (volume.restrict Wd) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ Kd, ∀ w ∈ Kd,
        ‖V z - V w‖ ≤ B * Real.sqrt ‖z - w‖) ∧
      ContDiffAt ℝ 1 (fun t : ℝ => (V (t : ℂ)).1) 0 := by
  let a := annulusPoint x (if upper then 1 else 0)
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
  let P := annulusBoundarySource r hr.ne' upper x
  let H := q ∘ A.map ∘ P
  obtain ⟨gE, DE, R, hR, hR1, hsrc, hH, hHi, hmetric, hconf, heq, hHinj⟩ :=
    annulus_strip_boundary_coordinate_data A hr x upper hminimum hAc hAi hconformal hinj
  have hsrc0 : c (sigma x) ∈ q.source := by
    rw [← htrace x]
    exact mem_chart_source _ _
  obtain ⟨hJ, hsJ, hcq, hcvq⟩ := regular_trace_in_chart hc (A.map a) hsrc0 (hcv (sigma x))
  let label := fun s : ℝ => sigma (x + r * s)
  have hlabel : ContDiff ℝ 1 label :=
    hsigma.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hlabel0 : label 0 = sigma x := by simp [label]
  have hlabelmono : Monotone label := fun s t hst =>
    hmono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hst hr.le))
  have hzero (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) :
      fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) z ≠ 0 := by
    intro hd
    have he : (1 : ℂ) = 0 := (hHinj z hz) (by rw [hd]; rfl)
    exact one_ne_zero he
  have hb (s : ℝ) (_hs : ‖(s : ℂ)‖ ≤ R) : H (s : ℂ) = (q ∘ c) (label s) := by
    simp only [H, P, Function.comp_apply, annulusBoundarySource_real, htrace, label]
  obtain ⟨d, hd, hdR, hframe⟩ := halfDisk_regular_arc_frame DE hR hJ hcq hlabel
    (Or.inl hlabelmono) (hlabel0.symm ▸ hsJ) (hlabel0.symm ▸ hcvq)
    hH hHi hb hconf heq hzero
  exact ⟨gE, DE, R, d, hR, hR1, hd, hdR,
    hsrc, hH, hHi, hmetric, hconf, heq, hframe⟩

end PoincareConjecture.M64
