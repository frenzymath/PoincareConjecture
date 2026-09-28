import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.GaugeMetricCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Geodesic












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)




theorem gauge_principal_contDiffOn (F : RicciFlow n M (Icc a b)) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × E) × E =>
        ((F.metric z.1.1).pullbackCoefficients (chartAt E p).symm z.1.2 z.2 z.2)⁻¹)
      ((Icc a b ×ˢ (chartAt E p).target) ×ˢ {V : E | V ≠ 0}) := by
  intro z hz
  have hB := (chart_metric_coefficients_contDiffOn F p z.1 hz.1).comp z
    (s := (Icc a b ×ˢ (chartAt E p).target) ×ˢ {V : E | V ≠ 0})
    contDiffWithinAt_fst (fun _ hw => hw.1)
  exact ((hB.clm_apply contDiffWithinAt_snd).clm_apply contDiffWithinAt_snd).inv
    (ne_of_gt (chart_metric_pairing_pos F p z.1.1 hz.1.2 hz.2))




theorem gauge_christoffel_contDiffOn (F : RicciFlow n M (Icc a b)) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × E) × E => coordinateChristoffel
        ((F.metric z.1.1).pullbackCoefficients (chartAt E p).symm) z.1.2 z.2 z.2)
      ((Icc a b ×ˢ (chartAt E p).target) ×ˢ univ) := by
  intro z hz
  have hB := (chart_metric_coefficients_contDiffOn F p z.1 hz.1).comp z
    (s := (Icc a b ×ˢ (chartAt E p).target) ×ˢ (univ : Set E))
    contDiffWithinAt_fst (fun _ hw => hw.1)
  have hD := (chart_metric_spatial_derivative_contDiffOn F p z.1 hz.1).comp z
    (s := (Icc a b ×ˢ (chartAt E p).target) ×ˢ (univ : Set E))
    contDiffWithinAt_fst (fun _ hw => hw.1)
  have hinv := (F.metric z.1.1).isInvertible_pullbackCoefficients
    (Proofs.M09.inverseChartDifferential_bijective p z.1.2 hz.1.2).1
  have hi : ContDiffWithinAt ℝ ∞
      (fun w : (ℝ × E) × E =>
        ((F.metric w.1.1).pullbackCoefficients (chartAt E p).symm w.1.2).inverse)
      ((Icc a b ×ˢ (chartAt E p).target) ×ˢ univ) z := by
    convert! hinv.contDiffAt_map_inverse.comp_contDiffWithinAt z hB using 1
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hflip' : ContDiff ℝ ∞
      (fun L : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff
  have hK : ContDiffWithinAt ℝ ∞
      (fun w : (ℝ × E) × E => metricKoszulCovector
        (fderiv ℝ ((F.metric w.1.1).pullbackCoefficients (chartAt E p).symm) w.1.2)
        w.2 w.2) ((Icc a b ×ˢ (chartAt E p).target) ×ˢ univ) z := by
    unfold metricKoszulCovector
    exact (((hD.clm_apply contDiffWithinAt_snd).clm_apply contDiffWithinAt_snd).add
      ((hflip.comp_contDiffWithinAt (hD.clm_apply contDiffWithinAt_snd)).clm_apply
        contDiffWithinAt_snd) |>.sub
      ((hflip.comp_contDiffWithinAt
        ((hflip'.comp_contDiffWithinAt hD).clm_apply contDiffWithinAt_snd)).clm_apply
          contDiffWithinAt_snd)).const_smul _
  exact hi.clm_apply hK




theorem gauge_rhs_contDiffOn (F : RicciFlow n M (Icc a b)) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ((ℝ × E) × E) × E =>
        ((F.metric z.1.1.1).pullbackCoefficients (chartAt E p).symm
          z.1.1.2 z.1.2 z.1.2)⁻¹ •
          (z.2 + coordinateChristoffel
            ((F.metric z.1.1.1).pullbackCoefficients (chartAt E p).symm)
            z.1.1.2 z.1.2 z.1.2))
      (((Icc a b ×ˢ (chartAt E p).target) ×ˢ {V : E | V ≠ 0}) ×ˢ univ) := by
  have hprincipal := (gauge_principal_contDiffOn F p).comp contDiffOn_fst
    (s := ((Icc a b ×ˢ (chartAt E p).target) ×ˢ {V : E | V ≠ 0}) ×ˢ (univ : Set E))
    (fun _ hz => hz.1)
  have hchristoffel := (gauge_christoffel_contDiffOn F p).comp contDiffOn_fst
    (s := ((Icc a b ×ˢ (chartAt E p).target) ×ˢ {V : E | V ≠ 0}) ×ˢ (univ : Set E))
    (fun _ hz => ⟨hz.1.1, mem_univ _⟩)
  exact hprincipal.smul (contDiffOn_snd.add hchristoffel)

end PoincareConjecture.M63
