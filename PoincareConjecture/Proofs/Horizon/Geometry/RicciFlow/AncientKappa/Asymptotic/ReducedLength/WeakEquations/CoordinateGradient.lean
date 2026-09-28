import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakEquations
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakEquations.Coordinates








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory VectorField
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem LeviCivitaData.differential_gradient_in_coordinates
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e x)) :
    mvfderiv (𝓡 n) f (e x) (D.gradient φ (e x)) =
      fderiv ℝ (φ ∘ e) x
        ((g.pullbackCoefficients e x).inverse (fderiv ℝ (f ∘ e) x)) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hi : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  have hchain := congrArg (fun A => A (mpullback (𝓡 n) (𝓡 n) e (D.gradient φ) x))
    (mvfderiv_comp x hf (hD.mdifferentiableAt hx))
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at hchain
  have hleft : fderiv ℝ (f ∘ e) x (mpullback (𝓡 n) (𝓡 n) e (D.gradient φ) x) =
      mvfderiv (𝓡 n) f (e x) (D.gradient φ (e x)) := by
    change fderiv ℝ (f ∘ e) x (mpullback (𝓡 n) (𝓡 n) e (D.gradient φ) x) =
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x (mpullback (𝓡 n) (𝓡 n) e (D.gradient φ) x))
      at hchain
    change _ = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e x) (D.gradient φ (e x))
    simpa only [mpullback, hi.self_apply_inverse] using hchain
  rw [← hleft, D.coordinateGradient_eq_inverse_fderiv e he hei hφ hx,
    LeviCivitaData.pullback_inverse_pairing_comm g (hD.mfderiv_injective hx)]

namespace AncientAsymptoticSolitonPredecessors

open LeviCivitaData.Dirichlet

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem reducedLength_second_weak_coordinate_gradient_inequality
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
    let B := fun x => (φ x *
      (-fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) +
        D.scalarCurvature (e x) + (l x - (n : ℝ)) / τ) -
      2 * fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x))) *
      g.pullbackVolumeDensity e x
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  let g := K.flow.metric (0 - τ)
  let D := K.flow.connection (0 - τ)
  let ψ := coordinateExtension e φ
  let l := fun q => reducedLength K.flow 0 p q τ
  let B := fun q => ψ q * (-reducedLengthGradientNormSq K.flow 0
    (fun z => reducedLength K.flow 0 p z.1 z.2) τ q +
    D.scalarCurvature q + (l q - (n : ℝ)) / τ)
  let d := fun q => mvfderiv (𝓡 n) l q (D.gradient ψ q)
  let F := fun q => B q - 2 * d q
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
  have hw := P.reducedLength_second_weak_gradient_inequality p hτ hψ hψc hψ0
  simp only [calibratedMetricVolume_eq_volumeMeasure] at hw
  have hB : Integrable B g.volumeMeasure := hw.1
  have hd : Integrable d g.volumeMeasure := hw.2.1
  have hF : Integrable F g.volumeMeasure := hB.sub (hd.const_mul 2)
  have hFi : (∫ q, F q ∂g.volumeMeasure) ≤ 0 := by
    dsimp only [F]
    rw [integral_sub hB (hd.const_mul 2), integral_const_mul]
    exact hw.2.2
  have hFzero {y : M} (hy : y ∉ tsupport ψ) : F y = 0 := by
    dsimp only [F, B, d]
    rw [image_eq_zero_of_notMem_tsupport hy, D.gradient_eq_zero_of_notMem_tsupport hy]
    simp only [map_zero, mul_zero, zero_mul, sub_zero]
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
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨R⟩ := V.measure_regularity p
  have hae := ae_regular_in_coordinates R hτ (by linarith) e he hei
  have heq : (fun x => F (e x) * g.pullbackVolumeDensity e x) =ᵐ[volume.restrict O]
      (fun x => (φ x *
        (-fderiv ℝ (l ∘ e) x ((g.pullbackCoefficients e x).inverse (fderiv ℝ (l ∘ e) x)) +
          D.scalarCurvature (e x) + (l (e x) - (n : ℝ)) / τ) -
        2 * fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ (l ∘ e) x))) *
          g.pullbackVolumeDensity e x) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hO.measurableSet] with x hx hxO
    obtain ⟨r⟩ := R.regular_points (e x, τ) (hx (hOs hxO))
    have hl : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) l (e x) :=
      (regular_reducedLength_spatial_smooth r).mdifferentiableAt (by simp)
    have hψφ : (ψ ∘ e) =ᶠ[𝓝 x] φ := by
      filter_upwards [e.open_source.mem_nhds (hOs hxO)] with y hy
      exact coordinateExtension_comp_apply e φ hy
    have hnorm := D.gradient_norm_sq_eq_inverse_pairing e he hei (hOs hxO) hl
    have hpair := D.differential_gradient_in_coordinates e he hei hψ (hOs hxO) hl
    rw [hψφ.fderiv_eq] at hpair
    dsimp only [F, B, d]
    rw [show ψ (e x) = φ x from coordinateExtension_comp_apply e φ (hOs hxO),
      reducedLengthGradientNormSq_eq_gradient_norm_sq, hnorm, hpair]
  refine ⟨(hi.mono_set hOs).congr heq, ?_⟩
  change (∫ x in O, _) ≤ 0
  dsimp only [g, D, l, Function.comp_def] at heq
  rw [← integral_congr_ae heq, ← hrestrict, ← hchange, htotal]
  exact hFi

end AncientAsymptoticSolitonPredecessors
end PoincareConjecture
