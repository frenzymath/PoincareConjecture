import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.CoordinateIntegral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

open LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem reducedLength_second_weak_coordinate_inequality
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O) (hOs : O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let g := K.flow.metric (0 - τ)
    let D := K.flow.connection (0 - τ)
    let l := fun x => reducedLength K.flow 0 p (e x) τ
    let ψ := coordinateExtension e φ
    let B := fun x => (φ x *
      (-fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) +
        D.scalarCurvature (e x) + (l x - (n : ℝ)) / τ) +
      2 * l x * D.laplacian ψ (e x)) * g.pullbackVolumeDensity e x
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  let g := K.flow.metric (0 - τ)
  let D := K.flow.connection (0 - τ)
  let ψ := coordinateExtension e φ
  let F := reducedLengthSecondWeakIntegrand K.flow 0 p τ ψ
  have hφs : tsupport φ ⊆ e.source := hφO.trans hOs
  have hψ := contMDiff_coordinateExtension e hei hφ hφc hφs
  have hψc := hasCompactSupport_coordinateExtension e hφc hφs
  have hψs : tsupport ψ ⊆ e.target := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := tsupport_coordinateExtension_subset_image e hφc hφs hy
    exact e.map_source (hφs hx)
  have hψ0 : ∀ y, 0 ≤ ψ y := by
    intro y
    dsimp only [ψ, coordinateExtension]
    by_cases hy : y ∈ e.target
    · simpa only [indicator_of_mem hy, Function.comp_apply] using hφ0 (e.symm y)
    · simp only [indicator_of_notMem hy, le_refl]
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  have hw := V.weak_inequalities p τ hτ (by linarith) ψ hψ hψc hψ0
  simp_rw [calibratedMetricVolume_eq_volumeMeasure] at hw
  have hF : Integrable F g.volumeMeasure := hw.2.1
  have hFzero {y : M} (hy : y ∉ tsupport ψ) : F y = 0 := by
    dsimp only [F, reducedLengthSecondWeakIntegrand]
    rw [image_eq_zero_of_notMem_tsupport hy, D.laplacian_eq_zero_of_notMem_tsupport hy]
    ring
  obtain ⟨hi, hchange⟩ := g.integrableOn_integral_pullback_density e he hei hF.integrableOn
  have htotal : (∫ y in e.target, F y ∂g.volumeMeasure) = ∫ y, F y ∂g.volumeMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hFzero (fun hs => hy (hψs hs)))
  have hzero {x : EuclideanSpace ℝ (Fin n)} (hxs : x ∈ e.source) (hxO : x ∉ O) :
      F (e x) * g.pullbackVolumeDensity e x = 0 := by
    have hx : e x ∉ tsupport ψ := by
      intro hs
      obtain ⟨y, hy, hyx⟩ := tsupport_coordinateExtension_subset_image e hφc hφs hs
      exact hxO ((e.injOn (hφs hy) hxs hyx) ▸ hφO hy)
    rw [hFzero hx, zero_mul]
  have hrestrict : (∫ x in e.source, F (e x) * g.pullbackVolumeDensity e x) =
      ∫ x in O, F (e x) * g.pullbackVolumeDensity e x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_source.measurableSet hOs
      (fun x hx => hzero hx.1 hx.2)
  have hae := P.reducedLengthGradientNormSq_coordinates_ae p hτ e he hei
  have heq : (fun x => F (e x) * g.pullbackVolumeDensity e x) =ᵐ[volume.restrict O]
      (fun x => (φ x *
        (-fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) τ) x
          ((g.pullbackCoefficients e x).inverse
            (fderiv ℝ (fun y => reducedLength K.flow 0 p (e y) τ) x)) +
          D.scalarCurvature (e x) + (reducedLength K.flow 0 p (e x) τ - (n : ℝ)) / τ) +
        2 * reducedLength K.flow 0 p (e x) τ * D.laplacian ψ (e x)) *
          g.pullbackVolumeDensity e x) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hO.measurableSet] with x hx hxO
    dsimp only [F, reducedLengthSecondWeakIntegrand, ψ, D, g]
    rw [coordinateExtension_comp_apply e φ (hOs hxO), hx (hOs hxO)]
  refine ⟨(hi.mono_set hOs).congr heq, ?_⟩
  change (∫ x in O, _) ≤ 0
  rw [← integral_congr_ae heq, ← hrestrict, ← hchange, htotal]
  exact hw.2.2.2

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
