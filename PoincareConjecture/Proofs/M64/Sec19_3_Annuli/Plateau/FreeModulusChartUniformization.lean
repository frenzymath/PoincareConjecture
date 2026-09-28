import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusChartDisjointAnnulus
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFreeModulusApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.M64

local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)

theorem exists_disjoint_chart_free_uniformization
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M}
    {cchart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hn : 3 ≤ n) {eps : ℝ} (heps : 0 < eps)
    {d c : ℝ → M}
    (hsourceD : ∀ x, d x ∈ cchart.source)
    (hsourceC : ∀ x, c x ∈ cchart.source)
    (hcoordD : ContDiff ℝ 1 (fun x => cchart (d x)))
    (hcoordC : ContDiff ℝ 1 (fun x => cchart (c x)))
    (hperiodD : Function.Periodic d curvePeriod)
    (hperiodC : Function.Periodic c curvePeriod)
    (hchartSymm : ContMDiffOn (𝓡 n) (𝓡 n) 1 cchart.symm cchart.target)
    (A0 : M64Annulus g d c) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ < eps ∧
      (∀ x, cchart (c x) + v ∈ cchart.target) ∧
      Function.Periodic (fun x => cchart.symm (cchart (c x) + v)) curvePeriod ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart.symm (cchart (c x) + v)) ∧
      Disjoint (range d)
        (range (fun x => cchart.symm (cchart (c x) + v))) ∧
      ∃ A : M64Annulus g d
          (fun x => cchart.symm (cchart (c x) + v)),
        ∃ r : ℝ, 0 < r ∧
          ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
            ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
            StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
            (∀ x : ℝ, 0 < deriv sigma0.map x) ∧
            (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
            ∃ B : M64Annulus g
                (d ∘ sigma0.map)
                ((fun x => cchart.symm (cchart (c x) + v)) ∘ sigma1.map),
              ContMDiffOn (𝓡 2) (𝓡 n) 1 B.map Strip ∧
              IntegrableOn (fun p =>
                (r * m60AreaGram g B.map p 0 0 +
                  r⁻¹ * m60AreaGram g B.map p 1 1) / 2)
                m64AnnulusDomain ∧
              m64ClassicalWeightedGramEnergy g B r < A.area + eps := by
  have hDMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 d := by
    have hcoordMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart (d x)) :=
      contMDiff_iff_contDiff.mpr hcoordD
    have hcomp := hchartSymm.comp_contMDiff hcoordMD
      (fun x => cchart.map_source (hsourceD x))
    convert hcomp using 1
    funext x
    exact (cchart.left_inv (hsourceD x)).symm
  obtain ⟨v, hv, hvtarget, hvperiod, hcv, hvdisjoint, A, hA⟩ :=
    exists_disjoint_chart_boundary_annulus hn heps hsourceD hsourceC hcoordD
      hcoordC hperiodD hperiodC hchartSymm A0
  obtain ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, hE⟩ :=
    M64Uniformization.exists_free_annulus_energy_lt_area A hDMD hcv heps
  refine ⟨v, hv, hvtarget, hvperiod, hcv, hvdisjoint, A, r, hr, sigma0, sigma1,
    hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, hE⟩

theorem exists_disjoint_chart_free_modulus_supplier
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M}
    {cchart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hn : 3 ≤ n) {eps : ℝ} (heps : 0 < eps)
    {d c : ℝ → M}
    (hsourceD : ∀ x, d x ∈ cchart.source)
    (hsourceC : ∀ x, c x ∈ cchart.source)
    (hcoordD : ContDiff ℝ 1 (fun x => cchart (d x)))
    (hcoordC : ContDiff ℝ 1 (fun x => cchart (c x)))
    (hperiodD : Function.Periodic d curvePeriod)
    (hperiodC : Function.Periodic c curvePeriod)
    (hchartSymm : ContMDiffOn (𝓡 n) (𝓡 n) 1 cchart.symm cchart.target) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ < eps ∧
      (∀ x, cchart (c x) + v ∈ cchart.target) ∧
      Function.Periodic (fun x => cchart.symm (cchart (c x) + v)) curvePeriod ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart.symm (cchart (c x) + v)) ∧
      Disjoint (range d)
        (range (fun x => cchart.symm (cchart (c x) + v))) ∧
      M64FreeConformalModulusApproximation g d
        (fun x => cchart.symm (cchart (c x) + v)) := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  obtain ⟨v, hv, hvtarget, hvperiod, -, hcprime, -, hvdisjoint⟩ :=
    exists_small_chart_displacement_disjoint_smooth hn hP heps hsourceD hsourceC
      hcoordD hcoordC hperiodD hperiodC hchartSymm
  have hDMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 d := by
    have hcoordMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart (d x)) :=
      contMDiff_iff_contDiff.mpr hcoordD
    have hcomp := hchartSymm.comp_contMDiff hcoordMD
      (fun x => cchart.map_source (hsourceD x))
    convert hcomp using 1
    funext x
    exact (cchart.left_inv (hsourceD x)).symm
  have hfree := M64Uniformization.m64FreeConformalModulusApproximation_of_C1
    g hDMD hcprime
  exact ⟨v, hv, hvtarget, hvperiod, hcprime, hvdisjoint, hfree⟩

end PoincareConjecture.M64
