import PoincareConjecture.Proofs.M14.Sec6_2_EulerResidual

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem rawHorizontalCovariantDerivative_contMDiff
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (W : HorizontalSection G.spacetime)
    (hW : ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q (W q))) :
    ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod
        𝓘(ℝ, SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun q => Bundle.TotalSpace.mk'
        (SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun q => TangentSpace (spacetimeModel n) q →L[ℝ] G.Horizontal q)
        q (rawHorizontalCovariantDerivative G.leafwise W q)) := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  obtain ⟨C⟩ := H.horizontal_connection
  have hCW := C.smooth.contMDiff.contMDiff (hW.contMDiffOn.of_le (by simp))
  apply (contMDiffOn_univ.mp hCW).congr
  intro q
  rw [C.raw_eq univ isOpen_univ W hW.contMDiffOn q (mem_univ q)]

theorem horizontalScalarDifferential_contMDiff
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (W : HorizontalSection G.spacetime)
    (hW : ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q (W q))) :
    ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (fun q => M14HorizontalScalarDifferential G q (W q).val) := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hI : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (spacetimeModel n).tangent ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
        Bundle.TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : G.Point → Type _)) v.proj v.2.val) :=
    G.spacetime.horizontal_inclusion_smooth
  have hT := (H.scalar_smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (hI.comp hW)
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ (𝓘(ℝ, ℝ))).comp hT

private theorem horizontalMetric_pair_contDiffOn {γ : ℝ → G.Point} {J : Set ℝ}
    {Y Z : ∀ s, G.Horizontal (γ s)}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ γ J)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Y s)) J)
    (hZ : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Z s)) J) :
    ContDiffOn ℝ ∞ (fun s => G.spacetime.horizontalMetric.inner (γ s) (Y s) (Z s)) J := by
  have hpair := (G.spacetime.horizontalMetric.contMDiff.comp_contMDiffOn hγ).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial G.Point ℝ) hY hZ
  apply ContMDiffOn.contDiffOn
  intro s hs
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffWithinAt_totalSpace.mp (hpair s hs)).2

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem squareRootEulerResidual_stationary_continuousOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) (W : HorizontalSection G.spacetime)
    (hW : ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q (W q))) :
    ContinuousOn (fun s => M14SquareRootEulerResidual G R E s (W (R.curve s)))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  let C := M14SqrtParameterInterval τ₁ τ₂
  let B := fun s => G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (W (R.curve s))
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hR := R.smooth.mono R.interval_subset
  have hA := squareRoot_horizontalVelocity_smooth R
  have hB : ContDiffOn ℝ ∞ B C := horizontalMetric_pair_contDiffOn hR hA
    (hW.comp_contMDiffOn hR)
  have hvelocity := hR.contMDiffOn_mfderivWithin_const_apply hC (1 : ℝ)
    (k := ∞) (by simp)
  have hraw := (rawHorizontalCovariantDerivative_contMDiff hM12 W hW).comp_contMDiffOn hR
  have hDW := hraw.clm_bundle_apply hvelocity
  have hconnection := horizontalMetric_pair_contDiffOn hR hA hDW
  have hscalar := ((horizontalScalarDifferential_contMDiff hM12 W hW).comp_contMDiffOn
    hR).contDiffOn
  have hweight : ContDiffOn ℝ ∞ (fun s : ℝ => 2 * s ^ 2) C :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hcont := (((hB.derivWithin hC (m := ∞) (by simp)).sub hconnection).sub
    (hweight.mul hscalar)).continuousOn
  apply hcont.congr
  intro s hs
  have hd := horizontalCovariantDerivative_metric_derivative E hs (hC s hs)
    ((hR s hs).mdifferentiableWithinAt (by simp)) W (hW (R.curve s))
  rw [squareRoot_velocity_clock R hs] at hd
  have hdB : HasDerivWithinAt B _ C s := hd.congr_of_mem
    (fun r hr => by simp only [B, E.agrees r hr]) hs
  have hderiv := hdB.derivWithin (hC s hs)
  change M14SquareRootEulerResidual G R E s (W (R.curve s)) =
    derivWithin B C s - _ - 2 * s ^ 2 *
      M14HorizontalScalarDifferential G (R.curve s) (W (R.curve s)).val
  unfold M14SquareRootEulerResidual M14SquareRootVelocity
  linarith

end PoincareConjecture.M14
