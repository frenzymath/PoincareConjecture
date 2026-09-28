import PoincareConjecture.Proofs.M14.Sec6_4_IndexPair
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoefficients
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCover
import PoincareConjecture.Proofs.M14.Sec6_2_EulerResidual
import PoincareConjecture.Proofs.M08.IndexPairAlgebra










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem five_horizontal_eval_heq
    (F : ∀ q, G.Horizontal q → G.Horizontal q → G.Horizontal q →
      G.Horizontal q → G.Horizontal q → ℝ)
    {q r : G.Point} (h : q = r)
    {A Y Z DY DZ : G.Horizontal q} {A' Y' Z' DY' DZ' : G.Horizontal r}
    (hA : HEq A A') (hY : HEq Y Y') (hZ : HEq Z Z')
    (hDY : HEq DY DY') (hDZ : HEq DZ DZ') :
    F q A Y Z DY DZ = F r A' Y' Z' DY' DZ' := by
  cases h
  cases hA
  cases hY
  cases hZ
  cases hDY
  cases hDZ
  rfl

private theorem cast_equiv_coordinates {q r : G.Point} (h : q = r)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] G.Horizontal q) (v : G.Horizontal r) :
    HEq v (e ((h ▸ e).symm v)) := by
  cases h
  exact heq_of_eq (e.apply_symm_apply v).symm

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)




theorem horizontalIndexPairDensity_gauge (b : G.gaugeCover.index)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
    {a c : ℝ} (hac : a < c) (hsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
    (hrec : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s)
    (hclock : ∀ s ∈ Icc a c, (β s).1.val = T - s ^ 2)
    {s : ℝ} (hs : s ∈ Icc a c) {Y Z DY DZ : G.Horizontal (R.curve s)}
    (v w d e : EuclideanSpace ℝ (Fin n))
    (hY : HEq Y ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 v))
    (hZ : HEq Z ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 w))
    (hDY : HEq DY ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 d))
    (hDZ : HEq DZ ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 e)) :
    horizontalIndexPairDensity R s Y Z DY DZ =
      M08.chartActionMetric W.flow T x₀ (s, (β s).2.val) d e +
        M08.closedChartJacobiPotential W.flow T x₀ (Icc a c) (s, (β s).2.val)
          (derivWithin (fun r => (β r).2.val) (Icc a c) s) v w := by
  have htime (r : ℝ) (hr : r ∈ Icc a c) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr]
    exact (β r).1.property
  have hA := squareRootVelocity_gauge_subset b R hsub hβ hrec hs (uniqueDiffOn_Icc hac s hs)
  let φ := fun (q : G.Point) (A Y Z DY DZ : G.Horizontal q) =>
    G.spacetime.horizontalMetric.inner q DY DZ - horizontalRiemann G.leafwise q Y A Z A +
      2 * s * M14BcalPairing G q A Y Z + 2 * s ^ 2 * M14HorizontalHessianPairing G q Y Z -
      4 * s * M14HorizontalRicciDerivativePairing G q Y A Z
  have hgeom := five_horizontal_eval_heq φ (hrec s hs).symm hA hY hZ hDY hDZ
  change φ (R.curve s) (R.horizontal_velocity s) Y Z DY DZ = _
  rw [hgeom]
  rw [gauge_chartActionMetric b W T x₀ (β s).2 s (β s).1 (hclock s hs).symm,
    gauge_closedJacobiPotential b hCoordinates W hM04 T hac htime x₀ (β s).2 hs (β s).1
      (hclock s hs).symm hscalar]
  dsimp only [φ]
  ring

private theorem indexPair_coordinate_forms
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    ∃ j : EuclideanSpace ℝ (Fin n) ≃L[ℝ] G.Horizontal (R.curve s),
      ∃ B C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        (∀ v w, B v w = B w v) ∧ (∀ v w, C v w = C w v) ∧
        ∀ Y Z DY DZ : G.Horizontal (R.curve s),
          horizontalIndexPairDensity R s Y Z DY DZ =
            B (j.symm DY) (j.symm DZ) + C (j.symm Y) (j.symm Z) := by
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  obtain ⟨b, N, β, hN, hsN, hβ, hrec, hclock⟩ := exists_squareRoot_gauge_neighborhood R hs
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  obtain ⟨l, r, hal, hlr, hrb, hls, hsr, hsubN, hnear⟩ :=
    M08.exists_enlarged_closed_interval hab hs.1 le_rfl hs.2 hN
      (by simpa only [Icc_self, singleton_subset_iff] using hsN)
  have hsub : Icc l r ⊆ M14SqrtParameterInterval τ₁ τ₂ := Icc_subset_Icc hal hrb
  have hsub' : Icc l r ⊆ M14SqrtParameterInterval τ₁ τ₂ ∩ N :=
    fun _ hv => ⟨hsub hv, hsubN hv⟩
  have hs' : s ∈ Icc l r := ⟨hls, hsr⟩
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  let x₀ := (β s).2
  let q := fun v => (β v).2.val
  let A := derivWithin q (Icc l r) s
  let B := M08.chartActionMetric W.flow T x₀ (s, q s)
  let C := M08.closedChartJacobiPotential W.flow T x₀ (Icc l r) (s, q s) A
  let e := (G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
  let j : EuclideanSpace ℝ (Fin n) ≃L[ℝ] G.Horizontal (R.curve s) :=
    hrec s (hsub' hs') ▸ e
  have htime (v : ℝ) (hv : v ∈ Icc l r) : T - v ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock v (hsub' hv)]
    exact (β v).1.property
  have hx : (β s).2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source :=
    mem_chart_source _ _
  have he : extChartAt (𝓡 n) x₀ (β s).2 = q s := by
    rw [extChartAt_coe]
    rfl
  have htarget := (extChartAt (𝓡 n) x₀).map_source
    (show (β s).2 ∈ (extChartAt (𝓡 n) x₀).source from by
      simpa only [extChartAt_source] using hx)
  refine ⟨j, B, C, ?_, ?_, ?_⟩
  · intro v w
    simpa only [he] using M08.chartActionMetric_symm_at W.flow T hx s v w
  · intro v w
    simpa only [he] using M08.closedChartJacobiPotential_symm W.flow hM04 T
      (uniqueDiffOn_Icc hlr) htime hx hs'
      (M08.mem_closure_interior_Icc_prod hlr (isOpen_extChartAt_target (I := 𝓡 n) x₀)
        hs' htarget) A v w
  · intro Y Z DY DZ
    exact horizontalIndexPairDensity_gauge R b hCoordinates hscalar W hM04 x₀ hlr hsub
      (hβ.mono hsub') (fun v hv => hrec v (hsub' hv)) (fun v hv => hclock v (hsub' hv))
      hs' (j.symm Y) (j.symm Z) (j.symm DY) (j.symm DZ)
      (cast_equiv_coordinates (hrec s (hsub' hs')) e Y)
      (cast_equiv_coordinates (hrec s (hsub' hs')) e Z)
      (cast_equiv_coordinates (hrec s (hsub' hs')) e DY)
      (cast_equiv_coordinates (hrec s (hsub' hs')) e DZ)



theorem horizontalIndexPairDensity_symm
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (Y Z DY DZ : G.Horizontal (R.curve s)) :
    horizontalIndexPairDensity R s Y Z DY DZ = horizontalIndexPairDensity R s Z Y DZ DY := by
  obtain ⟨j, B, C, hB, hC, h⟩ := indexPair_coordinate_forms R hM04 hM12 hs
  rw [h, h, hB, hC]




theorem horizontalIndexPairDensity_smul_right
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (Y Z DY DZ : G.Horizontal (R.curve s)) (c : ℝ) :
    horizontalIndexPairDensity R s Y (c • Z) DY (c • DZ) =
      c * horizontalIndexPairDensity R s Y Z DY DZ := by
  obtain ⟨j, B, C, hB, hC, h⟩ := indexPair_coordinate_forms R hM04 hM12 hs
  simp only [h, map_smul, smul_eq_mul]
  ring




theorem horizontalIndexPairDensity_quadratic
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (Y Z DY DZ : G.Horizontal (R.curve s)) (c : ℝ) :
    horizontalIndexPairDensity R s (Y + c • Z) (Y + c • Z) (DY + c • DZ) (DY + c • DZ) =
      horizontalIndexPairDensity R s Y Y DY DY +
        2 * c * horizontalIndexPairDensity R s Y Z DY DZ +
        c ^ 2 * horizontalIndexPairDensity R s Z Z DZ DZ := by
  obtain ⟨j, B, C, hB, hC, h⟩ := indexPair_coordinate_forms R hM04 hM12 hs
  have hsym := horizontalIndexPairDensity_symm R hM04 hM12 hs Y Z DY DZ
  simp only [h] at hsym ⊢
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  linear_combination -c * hsym



theorem horizontalJacobiPairResidual_smul_right
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (Y P DP Z : G.Horizontal (R.curve s)) (c : ℝ) :
    horizontalJacobiPairResidual R s Y P DP (c • Z) =
      c * horizontalJacobiPairResidual R s Y P DP Z := by
  have h₁ := horizontalIndexPairDensity_green_value R s Y (c • Z) P 0 DP
  have h₂ := horizontalIndexPairDensity_green_value R s Y Z P 0 DP
  have hI := horizontalIndexPairDensity_smul_right R hM04 hM12 hs Y Z P 0 c
  simp only [smul_zero] at hI
  rw [hI] at h₁
  simp only [map_smul, smul_eq_mul, horizontalRicci_smul_right hM12, map_zero] at h₁ h₂
  linear_combination h₁ - c * h₂

end PoincareConjecture.M14
