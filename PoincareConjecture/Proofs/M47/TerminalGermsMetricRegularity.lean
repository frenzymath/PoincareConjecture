import PoincareConjecture.Proofs.M47.TerminalGermsSpatialJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.CoordinateRicci

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {g : ℝ → RiemannianMetric n M}

theorem terminalGerms_metric_coefficients_within
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) {t : ℝ} (ht : t ∈ J) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (J ×ˢ univ) (t, x) := by
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg hf ht
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [RiemannianMetric.constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2)) (t, x) :=
    contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
  convert! (hc.comp (t, x) hid.contMDiffWithinAt (fun p hp => hp)).contDiffWithinAt using 1

theorem terminalGerms_metric_coefficients_on
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → M}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (J ×ˢ U) := by
  intro p hp
  exact (terminalGerms_metric_coefficients_within hg (hf p.2 hp.2) hp.1).mono
    (prod_mono subset_rfl (subset_univ U))

theorem terminalGerms_continuousOn_ricci
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : ∀ t, LeviCivitaData (g t)) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t => (D t).ricci x v w) J := by
  let c := extChartAt (𝓡 n) x
  have hc : ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients c.symm p.2)
      (J ×ˢ c.target) := by
    apply terminalGerms_metric_coefficients_on hg
    intro y hy
    exact (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  intro t ht
  apply LeviCivitaData.tendsto_ricci_of_coordinate_jets D (D t) x v w
  intro r _ a b
  have hscalar := (hc.clm_apply
    (contDiffOn_const (c := EuclideanSpace.basisFun (Fin n) ℝ a))).clm_apply
      (contDiffOn_const (c := EuclideanSpace.basisFun (Fin n) ℝ b))
  have hjet := terminalGerms_contDiffOn_spatial_jets (isOpen_extChartAt_target x) hscalar r
  have htime := hjet.continuousOn.comp
    (continuous_id.prodMk (continuous_const (y := c x))).continuousOn
    (show MapsTo (fun s : ℝ => (s, c x)) J (J ×ˢ c.target) from
      fun s hs => ⟨hs, mem_extChartAt_target x⟩)
  exact htime t ht

end PoincareConjecture.M47
