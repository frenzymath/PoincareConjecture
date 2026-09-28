import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.TraceDerivatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Action
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.TraceComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.CompactTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem sqrtRegularPath_action {J : Set ℝ} {F : RicciFlow n M J}
    {T τ : ℝ} {q : BackwardTimePath F T 0 τ} (S : SqrtRegularPath q) :
    regularizedLAction F T τ S.curve = backwardLLength F T 0 τ q.curve := by
  rw [← (squarePath_action q).2]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_nonneg τ)
  intro s hs
  have heq : S.curve =ᶠ[𝓝 s] fun r => q.curve (r ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact S.agrees r (by simpa only [sqrtParameterInterval, Real.sqrt_zero]
      using Ioo_subset_Icc_self hr)
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  simp only [regularizedLIntegrand, curveVelocity, hd, heq.eq_of_nhds]
  congr 2
  exact congrArg (fun x : M => (F.metric (T - s ^ 2)).inner x
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun r => q.curve (r ^ 2)) s) 1)
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun r => q.curve (r ^ 2)) s) 1)) heq.eq_of_nhds

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational
open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

private theorem continuousOn_squareSpeed (K : AncientKappaSolution 2 M)
    {C : Set ℝ} {α : ℝ → M} (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ α C)
    (E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := 2) α C)) :
    ContinuousOn (fun s => (K.flow.metric (-(s ^ 2))).inner (α s)
      (curveVelocityWithin (n := 2) α C s) (curveVelocityWithin (n := 2) α C s)) C := by
  have hfield := E.smooth.comp (contMDiffOn_id.prodMk hα) (fun s hs => E.graph_mem s hs)
  have hA : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 2)) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) (α s)
        (curveVelocityWithin (n := 2) α C s)) C := by
    apply hfield.congr
    intro s hs
    dsimp only [Function.comp_def, id_eq]
    rw [E.agrees s hs]
  exact (movingMetric_pair_contMDiffOn K.flow (fun s : ℝ => -(s ^ 2)) α
    (fun s => curveVelocityWithin (n := 2) α C s)
    (fun s => curveVelocityWithin (n := 2) α C s)
    (contMDiffOn_id.pow 2).neg hα hA hA
    (fun s _ => neg_nonpos.mpr (sq_nonneg s))).continuousOn

private theorem continuousOn_scalar_squareCurve (K : AncientKappaSolution 2 M)
    {τ : ℝ} (hτ : 0 < τ) {α : ℝ → M}
    (hα : ContinuousOn α (Icc 0 (Real.sqrt τ))) :
    ContinuousOn (fun s => (K.flow.connection (-(s ^ 2))).scalarCurvature (α s))
      (Icc 0 (Real.sqrt τ)) := by
  apply (K.continuousOn_scalarCurvature_spacetime_Icc hτ).comp
    ((continuous_id.pow 2).neg.continuousOn.prodMk hα)
  intro s hs
  have hsq := (sq_le_sq₀ hs.1 (Real.sqrt_nonneg τ)).mpr hs.2
  rw [Real.sq_sqrt hτ.le] at hsq
  exact ⟨⟨neg_le_neg hsq, neg_nonpos.mpr (sq_nonneg s)⟩, mem_univ _⟩

theorem curvature_add_minimum_le_two_of_index_trace (K : AncientKappaSolution 2 M)
    {τ m : ℝ} (hτ : 0 < τ) (q : BackwardTimePath K.flow 0 0 τ)
    (S : SqrtRegularPath q)
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
      (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))))
    (heuler : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s)
    (hterminal : curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0)
    (haction : backwardLLength K.flow 0 0 τ q.curve = 2 * Real.sqrt τ * m)
    (D : ℝ → ℝ) (hD : IntervalIntegrable D volume 0 (Real.sqrt τ))
    (htrace : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      (Real.sqrt τ) ^ 2 * D s =
        2 - 4 * s ^ 2 * (K.flow.connection (-(s ^ 2))).scalarCurvature (S.curve s) +
          2 * s ^ 4 * ((K.flow.connection (-(s ^ 2))).laplacian
            (K.flow.connection (-(s ^ 2))).scalarCurvature (S.curve s) +
              (K.flow.connection (-(s ^ 2))).scalarCurvature (S.curve s) ^ 2) -
          s ^ 2 * (K.flow.connection (-(s ^ 2))).ricci (S.curve s)
            (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) s)
            (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) s))
    (hindex : 0 ≤ ∫ s in 0..Real.sqrt τ, D s) :
    τ * (K.flow.connection (-τ)).scalarCurvature (S.curve (Real.sqrt τ)) + m ≤ 2 := by
  let c := Real.sqrt τ
  let C := Icc (0 : ℝ) c
  let A := curveVelocityWithin (n := 2) S.curve C
  let R := fun s => (K.flow.connection (-(s ^ 2))).scalarCurvature (S.curve s)
  let V := fun s => (K.flow.metric (-(s ^ 2))).inner (S.curve s) (A s) (A s)
  let reaction := fun s => (K.flow.connection (-(s ^ 2))).laplacian
    (K.flow.connection (-(s ^ 2))).scalarCurvature (S.curve s) + R s ^ 2
  let gradient := fun s =>
    mvfderiv (𝓡 2) (K.flow.connection (-(s ^ 2))).scalarCurvature (S.curve s) (A s)
  let ricci := fun s => (K.flow.connection (-(s ^ 2))).ricci (S.curve s) (A s) (A s)
  have hc : 0 < c := Real.sqrt_pos.mpr hτ
  have hCdom : C ⊆ S.domain := by
    simpa only [C, c, sqrtParameterInterval, Real.sqrt_zero] using S.interval_subset
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ S.curve C := S.smooth.mono hCdom
  have hRc : ContinuousOn R C := K.continuousOn_scalar_squareCurve hτ hα.continuousOn
  have hVc : ContinuousOn V C := K.continuousOn_squareSpeed hα E
  have hαat (s : ℝ) (hs : s ∈ Ioo 0 c) :
      MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 2) S.curve s :=
    ((S.smooth s (hCdom (Ioo_subset_Icc_self hs))).contMDiffAt
      (S.open_domain.mem_nhds (hCdom (Ioo_subset_Icc_self hs)))).mdifferentiableAt (by simp)
  have hR (s : ℝ) (hs : s ∈ Ioo 0 c) :
      HasDerivAt R (-2 * s * reaction s + gradient s) s := by
    exact K.hasDerivAt_scalarCurvature_square_curve_within
      (by simpa only [C, interior_Icc] using hs) (ne_of_gt hs.1) (hαat s hs)
  have hV (s : ℝ) (hs : s ∈ Ioo 0 c) :
      HasDerivAt V (-4 * s * ricci s + 4 * s ^ 2 * gradient s) s := by
    exact K.hasDerivAt_speed_square_curve_of_euler E
      (by simpa only [C, interior_Icc] using hs) (ne_of_gt hs.1) (hαat s hs) (heuler s hs)
  have hVterminal : V c = 0 := by
    simp only [V, A, C, c, hterminal, map_zero]
  have hact : (∫ s in 0..c, V s / 2 + 2 * s ^ 2 * R s) = 2 * c * m := by
    calc
      _ = regularizedLAction K.flow 0 τ S.curve := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc.le
        intro s hs
        have hvel : A s = curveVelocity (n := 2) S.curve s := by
          simp only [A, C, curveVelocityWithin, curveVelocity,
            mfderivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
        have hscalar := congrArg (fun t : ℝ => (K.flow.connection t).scalarCurvature (S.curve s))
          (zero_sub (s ^ 2))
        simp only [regularizedLIntegrand, V, R, hvel, zero_sub, hscalar]
        ring
      _ = backwardLLength K.flow 0 0 τ q.curve := sqrtRegularPath_action S
      _ = 2 * c * m := haction
  have hbound := ReducedLengthMinimum.Variation.curvature_add_minimum_le_two hc
    (Real.sq_sqrt hτ.le).symm R V reaction gradient ricci D
    hRc hVc hR hV hD htrace hVterminal hact hindex
  have hclock : -(c ^ 2) = -τ := congrArg Neg.neg (Real.sq_sqrt hτ.le)
  have hend := congrArg (fun t : ℝ => (K.flow.connection t).scalarCurvature (S.curve c)) hclock
  change τ * (K.flow.connection (-(c ^ 2))).scalarCurvature (S.curve c) + m ≤ 2 at hbound
  rw [hend] at hbound
  exact hbound

end PoincareConjecture.AncientKappaSolution
