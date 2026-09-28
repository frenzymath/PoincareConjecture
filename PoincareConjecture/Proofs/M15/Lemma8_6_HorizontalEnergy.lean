import PoincareConjecture.Definitions.M14PathCalculus
import PoincareConjecture.Statements.M12HorizontalTheory
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Bundle Filter Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem horizontal_energy_continuousOn
    {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}
    (E : M14PullbackExtension G γ J Y) (hγ : ContinuousOn γ J) :
    ContinuousOn (fun s => G.spacetime.horizontalMetric.inner (γ s) (Y s) (Y s)) J := by
  obtain ⟨U, _hU, hgraph, hjoint⟩ := E.joint_smooth
  let f : ℝ × G.Point → ℝ := fun z =>
    G.spacetime.horizontalMetric.inner z.2 (E.extension z.1 z.2) (E.extension z.1 z.2)
  have hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) 𝓘(ℝ) ∞ f U := by
    intro z hz
    have hmetric := (G.spacetime.horizontalMetric.contMDiff z.2).comp_contMDiffWithinAt
      z (contMDiffWithinAt_snd (I := 𝓘(ℝ, ℝ)) (J := spacetimeModel n) (s := U))
    exact (contMDiffWithinAt_totalSpace.mp
      (hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : G.Point => ℝ)
        (hjoint z hz) (hjoint z hz))).2
  have hcomp := hf.continuousOn.comp (continuousOn_id.prodMk hγ) hgraph
  exact hcomp.congr fun s hs => by
    simp only [Function.comp_apply, id_eq, f, E.agrees s hs]

theorem hasDerivAt_horizontal_energy
    (D : SpacetimeHorizontalConnection G.leafwise)
    {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}
    (E : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ interior J)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (spacetimeModel n) γ s) :
    HasDerivAt (fun r => G.spacetime.horizontalMetric.inner (γ r) (Y r) (Y r))
      (2 * G.spacetime.horizontalMetric.inner (γ s)
          (M14HorizontalCovariantDerivative G γ J Y E s) (Y s) +
        (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
          (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)) *
          horizontalMetricLieDerivative G.spacetime (γ s) (Y s) (Y s)) s := by
  have hsJ : s ∈ J := interior_subset hs
  have hJ : J ∈ 𝓝 s := mem_interior_iff_mem_nhds.mp hs
  obtain ⟨U, hU, hgraph, hjoint⟩ := E.joint_smooth
  let f : ℝ × G.Point → ℝ := fun z =>
    G.spacetime.horizontalMetric.inner z.2 (E.extension z.1 z.2) (E.extension z.1 z.2)
  have hf : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) 𝓘(ℝ) ∞ f (s, γ s) := by
    have he := (hjoint (s, γ s) (hgraph s hsJ)).contMDiffAt
      (hU.mem_nhds (hgraph s hsJ))
    have hmetric := (G.spacetime.horizontalMetric.contMDiff (γ s)).comp
      (s, γ s) (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := spacetimeModel n))
    exact (contMDiffAt_totalSpace.mp
      (hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : G.Point => ℝ) he he)).2
  obtain ⟨d, hd⟩ := E.parameter_derivative s hsJ
  have hparam : HasDerivAt (fun r => f (r, γ s))
      (2 * G.spacetime.horizontalMetric.inner (γ s) d (Y s)) s ∧
      deriv (fun r => E.extension r (γ s)) s = d := by

    let g := G.spacetime.horizontalMetric.toRiemannianMetric
    let : NormedAddCommGroup (G.Horizontal (γ s)) :=
      (g.toCore (γ s)).toNormedAddCommGroupOfTopology
        (g.continuousAt (γ s)) (g.isVonNBounded (γ s))
    let : NormedSpace ℝ (G.Horizontal (γ s)) :=
      (g.toCore (γ s)).toNormedSpaceOfTopology
        (g.continuousAt (γ s)) (g.isVonNBounded (γ s))
    refine ⟨?_, hd.deriv⟩
    have hp := ContinuousLinearMap.hasDerivAt_of_bilinear
      (B := G.spacetime.horizontalMetric.inner (γ s))
      (u := fun r => E.extension r (γ s)) (v := fun r => E.extension r (γ s))
      (u' := d) (v' := d) (x := s) (fun _ => hd) (fun _ => hd)
    have hp' : HasDerivAt (fun r => f (r, γ s))
        (G.spacetime.horizontalMetric.inner (γ s) (Y s) d +
          G.spacetime.horizontalMetric.inner (γ s) d (Y s)) s := by
      simpa only [f, E.agrees s hsJ] using hp
    rw [G.spacetime.horizontalMetric.symm (γ s) (Y s) d] at hp'
    convert hp' using 1
    ring
  obtain ⟨hparam, hdval⟩ := hparam
  have hDf : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      𝓘(ℝ, ℝ) f (s, γ s) := hf.mdifferentiableAt (by simp)
  have hmap := (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) s).prodMk hγ.hasMFDerivAt
  have hcomp := (hDf.hasMFDerivAt.comp s hmap).hasFDerivAt.hasDerivAt
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n) (I'' := 𝓘(ℝ, ℝ))
    (v := (1, mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)) hDf
  have hscalar : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r => f (r, γ s)) s 1 =
      2 * G.spacetime.horizontalMetric.inner (γ s) d (Y s) := by
    exact (congrArg (fun L : ℝ →L[ℝ] ℝ => L 1)
      (mfderiv_eq_fderiv (f := fun r => f (r, γ s)) (x := s))).trans hparam.deriv
  have htotal : HasDerivAt (fun r => f (r, γ r))
      (2 * G.spacetime.horizontalMetric.inner (γ s) d (Y s) +
        mvfderiv (spacetimeModel n) (fun p => f (s, p)) (γ s)
          (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)) s := by
    have hvalue := hsplit.trans (congrArg (· +
      mvfderiv (spacetimeModel n) (fun p => f (s, p)) (γ s)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)) hscalar)
    convert! hcomp using 1
    exact hvalue.symm
  have hspatial := D.metric_defect E.domain E.domain_open (E.extension s) (E.extension s)
    (E.spatial_smooth s) (E.spatial_smooth s) (γ s) (E.graph_mem s hsJ)
    (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)
  rw [D.raw_eq E.domain E.domain_open (E.extension s) (E.spatial_smooth s)
    (γ s) (E.graph_mem s hsJ), E.agrees s hsJ] at hspatial
  rw [G.spacetime.horizontalMetric.symm (γ s) (Y s)] at hspatial
  have hD : HasDerivAt (fun r => f (r, γ r))
      (2 * G.spacetime.horizontalMetric.inner (γ s)
          (M14HorizontalCovariantDerivative G γ J Y E s) (Y s) +
        (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
          (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)) *
          horizontalMetricLieDerivative G.spacetime (γ s) (Y s) (Y s)) s := by
    convert htotal using 1
    dsimp only [M14HorizontalCovariantDerivative]
    rw [mfderivWithin_of_mem_nhds hJ, hdval, map_add, add_apply]
    change _ = 2 * G.spacetime.horizontalMetric.inner (γ s) d (Y s) +
      mvfderiv (spacetimeModel n)
        (fun p => G.spacetime.horizontalMetric.inner p (E.extension s p) (E.extension s p))
        (γ s) (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)
    linarith only [hspatial]
  apply hD.congr_of_eventuallyEq
  filter_upwards [hJ] with r hr
  simp only [f, E.agrees r hr]

theorem hasDerivAt_square_energy
    (D : SpacetimeHorizontalConnection G.leafwise)
    {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hEuler : M14SquareRootEulerResidual G R E s (R.horizontal_velocity s) = 0) :
    HasDerivAt (fun r => G.spacetime.horizontalMetric.inner (R.curve r)
      (R.horizontal_velocity r) (R.horizontal_velocity r))
      (4 * s ^ 2 * M14HorizontalScalarDifferential G (R.curve s)
          (R.horizontal_velocity s).val -
        4 * s * horizontalRicci G.leafwise (R.curve s)
          (R.horizontal_velocity s) (R.horizontal_velocity s)) s := by
  have hsJ : s ∈ interior (M14SqrtParameterInterval τ₁ τ₂) := by
    simpa only [M14SqrtParameterInterval, interior_Icc] using hs
  have hJ : M14SqrtParameterInterval τ₁ τ₂ ∈ 𝓝 s := mem_interior_iff_mem_nhds.mp hsJ
  have hR : MDifferentiableAt 𝓘(ℝ, ℝ) (spacetimeModel n) R.curve s :=
    (R.smooth.contMDiffAt (mem_of_superset hJ R.interval_subset)).mdifferentiableAt (by simp)
  have hD := hasDerivAt_horizontal_energy D E hsJ hR
  have hvelocity := R.derivative_eq s (interior_subset hsJ)
  rw [mfderivWithin_of_mem_nhds hJ] at hvelocity
  have hhorizontal : mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (R.curve s)
      (R.horizontal_velocity s).val = 0 := (R.horizontal_velocity s).property
  have htime : (show ℝ from
      mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (R.curve s)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) R.curve s 1)) = -(2 * s) := by
    erw [hvelocity, map_add, map_smul, G.spacetime.timeVector_normalized, hhorizontal]
    simp only [smul_eq_mul, mul_one, add_zero]
  rw [htime, G.ricciEquation] at hD
  dsimp only [M14SquareRootEulerResidual, M14SquareRootVelocity] at hEuler
  convert hD using 1
  nlinarith only [hEuler]

end PoincareConjecture.Proofs.M15
