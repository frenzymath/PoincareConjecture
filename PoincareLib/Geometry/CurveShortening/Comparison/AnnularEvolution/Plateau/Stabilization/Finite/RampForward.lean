import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Finite.ProductForward
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Free.RampImmersedMinimum
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Flow.Lift
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Forward.MinimalCompetitor

/-! Actual separated ramps supply both sharp annular forward bounds.
The constructed minimum discharges every attainment, regularity and
immersion premise; the original C2 flows lift by constant sections.
Source: MT Lemma 19.15 and Corollary 19.16, pp. 447-449. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

/-- Actual separated C2 ramps satisfy both sharp original-base forward bounds. The displayed
original annulus guards the geometric class, and the minimum and all of its analytic data
are constructed internally. Source: Morgan--Tian Lemma 19.15, printed pp. 447-449, and Lemma
19.31, pp. 464-466;
`proof-work/tasks/M64/derivations/2026-09-26-finite-forward-competitors.md`. -/
theorem auxiliaryCircle_ramp_forward
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b)
    (hramp0 : M63IsRampAt P (fun x => c0 x t) t)
    (hramp1 : M63IsRampAt P (fun x => c1 x t) t)
    (A0 : M64Annulus (P.flow.metric t) (fun x => c0 x t) (fun x => c1 x t))
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < auxiliary) :
    let d0 := fun x s => auxiliaryCircleSection Q (Q.circle.quotient 0) (c0 x s)
    let d1 := fun x s => auxiliaryCircleSection Q (Q.circle.quotient delta) (c1 x s)
    let mu := m64FlowAnnulusArea Q d0 d1
    (∀ K : ℝ, 0 ≤ K → (∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) →
      AnnulusForwardDerivativeBound mu ((2 * (n : ℝ) - 1) * K * mu t) t) ∧
    (∀ K0 K1 K2 : ℝ, 0 ≤ K0 → CurveEvolutionAmbientBounds F K0 K1 K2 →
      AnnulusForwardDerivativeBound mu ((2 * (n : ℝ) - 1) * K0 * mu t) t) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let d0 := fun x s => auxiliaryCircleSection Q (Q.circle.quotient 0) (c0 x s)
  let d1 := fun x s => auxiliaryCircleSection Q (Q.circle.quotient delta) (c1 x s)
  let d := fun u : Bool => if u then d1 else d0
  have hd0 : M63C2ShrinkingCurveOn Q.flow d0 (Icc a b) :=
    auxiliaryCircle_c2ShrinkingCurve Q (Q.circle.quotient 0) hc0
  have hd1 : M63C2ShrinkingCurveOn Q.flow d1 (Icc a b) :=
    auxiliaryCircle_c2ShrinkingCurve Q (Q.circle.quotient delta) hc1
  have hd (u : Bool) : M63C2ShrinkingCurveOn Q.flow (d u) (Icc a b) := by
    cases u
    · exact hd0
    · exact hd1
  have ht' := Ioo_subset_Icc_self ht
  obtain ⟨r, hr, sigma0, sigma1, A, hAc, hAi, hs0, hs1, hminimum, hconformal, -, hinj⟩ :=
    auxiliaryCircle_free_ramp_immersed_minimum P Q t (fun x => c0 x t) (fun x => c1 x t)
      (hc0.spatial_regular t ht') (hc1.spatial_regular t ht') (hc0.periodic t ht')
      (hc1.periodic t ht') hramp0 hramp1 A0 hdelta hsmall
  let sigma := fun u : Bool => if u then sigma1 else sigma0
  have hsigma (u : Bool) : ContDiff ℝ 1 (sigma u).map := by
    cases u
    · exact hs0
    · exact hs1
  obtain ⟨B0, hB0⟩ := m64C2ShrinkingCurves_freeBoundaryAreaTransport Q.flow hd0 hd1 ht'
    sigma0 sigma1 A
  have hforward (rate : ℝ)
      (hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
        ∃ B : M64Annulus (Q.flow.metric (t + h))
            (fun x => d0 x (t + h)) (fun x => d1 x (t + h)),
          B.area ≤ A.area + h * (rate * A.area + eta)) :
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea Q d0 d1)
        (rate * m64FlowAnnulusArea Q d0 d1 t) t := by
    apply m64AnnulusForward_of_minimal_competitors B0 (hB0.trans hminimum)
    intro eta heta
    filter_upwards [hcomp eta heta] with h hh
    obtain ⟨B, hB⟩ := hh
    refine ⟨B, ?_⟩
    rw [hB0]
    change B.area ≤ A.area + h * (rate * m64LeastAnnulusArea (Q.flow.metric t)
      (fun x => d0 x t) (fun x => d1 x t) + eta)
    have hminimum' : A.area = m64LeastAnnulusArea (Q.flow.metric t)
        (fun x => d0 x t) (fun x => d1 x t) := hminimum
    rw [← hminimum']
    exact hB
  constructor
  · intro K hK hcurv
    exact hforward ((2 * (n : ℝ) - 1) * K)
      (auxiliaryCircle_finite_exists_forward P Q hn d hd ht sigma hsigma A hr
        hminimum hAc hAi hconformal (fun p hp => (hinj p hp).2.2) hK hcurv)
  · intro K0 K1 K2 hK0 hBounds
    exact hforward ((2 * (n : ℝ) - 1) * K0)
      (auxiliaryCircle_finite_exists_forward_of_ambient_bounds P Q hn d hd ht sigma hsigma A hr
        hminimum hAc hAi hconformal (fun p hp => (hinj p hp).2.2) hK0 hBounds)

end PoincareMT.M64
