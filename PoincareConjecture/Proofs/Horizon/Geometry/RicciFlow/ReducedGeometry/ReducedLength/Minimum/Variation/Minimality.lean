import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Action
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.BackwardPath
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Energy











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variation

open Geometry Variational

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def variationPath {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : LVariation F T a b p) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    BackwardTimePath F T a b := by
  have hmaps : MapsTo (fun t : ℝ ↦ (Real.sqrt t, u)) (Icc a b) V.squareDomain := by
    intro t ht
    exact V.square_contains ⟨⟨Real.sqrt_le_sqrt ht.1, Real.sqrt_le_sqrt ht.2⟩, hu⟩
  have hagrees (t : ℝ) (ht : t ∈ Icc a b) :
      V.squareFamily (Real.sqrt t) u = V.family t u := by
    have ht0 : 0 ≤ t := p.nonnegative.trans ht.1
    simpa only [Real.sq_sqrt ht0] using V.square_agrees (Real.sqrt t)
      ⟨Real.sqrt_le_sqrt ht.1, Real.sqrt_le_sqrt ht.2⟩ u hu
  refine {
    curve := fun t ↦ V.family t u
    nonnegative := p.nonnegative
    ordered := p.ordered
    terminal_mem := p.terminal_mem
    time_mem := p.time_mem
    continuous := ?_
    regular := ?_
    l_integrable := V.l_integrable u hu }
  · exact (V.square_smooth.continuousOn.comp
      (Real.continuous_sqrt.prodMk continuous_const).continuousOn hmaps).congr
        (fun t ht ↦ (hagrees t ht).symm)
  · have hsqrt : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1 Real.sqrt (Ioo a b) := by
      intro t ht
      exact (Real.contDiffAt_sqrt
        (ne_of_gt (p.nonnegative.trans_lt ht.1))).contMDiffAt.contMDiffWithinAt
    exact ((V.square_smooth.of_le (by simp)).comp
      (hsqrt.prodMk contMDiffOn_const) (hmaps.mono_left Ioo_subset_Icc_self)).congr
        (fun t ht ↦ (hagrees t (Ioo_subset_Icc_self ht)).symm)


theorem variationSquareAction_eq_variationLLength {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (V : LVariation F T a b p) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    variationSquareAction V u = variationLLength V u := by
  let q := variationPath V hu
  change (∫ s in Real.sqrt a..Real.sqrt b,
    regularizedLIntegrand F T (fun r ↦ V.squareFamily r u) s) =
      backwardLLength F T a b q.curve
  rw [backwardLLength_eq_transformed q]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt p.ordered.le)
  intro s hs
  have hs0 := (sq_mem_backward_interior p.nonnegative hs).1
  have ht := (sq_mem_backward_interior p.nonnegative hs).2
  have hbase : V.squareFamily s u = q.curve (s ^ 2) :=
    V.square_agrees s (Ioo_subset_Icc_self hs) u hu
  have hnear : (fun r ↦ V.squareFamily r u) =ᶠ[𝓝 s] fun r ↦ q.curve (r ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact V.square_agrees r (Ioo_subset_Icc_self hr) u hu
  have hreg := (q.regular (s ^ 2) ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)
  have hvel : curveVelocity (n := n) (fun r ↦ V.squareFamily r u) s =
      (2 * s) • curveVelocity (n := n) q.curve (s ^ 2) := by
    have heq : curveVelocity (n := n) (fun r ↦ V.squareFamily r u) s =
        curveVelocity (n := n) (fun r ↦ q.curve (r ^ 2)) s := by
      unfold curveVelocity
      rw [hnear.mfderiv_eq]
      rfl
    exact heq.trans (curveVelocity_comp_sq (hreg.mdifferentiableAt one_ne_zero))
  unfold regularizedLIntegrand backwardLIntegrand
  dsimp only
  rw [Real.sqrt_sq hs0.le]
  simp only [hvel, map_smul, smul_apply, smul_eq_mul]
  rw [hbase]
  ring


theorem isLocalMin_variationSquareAction {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (hmin : ∀ q : BackwardTimePath F T a b, q.curve a = p.curve a →
      backwardLLength F T a b p.curve ≤ backwardLLength F T a b q.curve)
    (V : InitialFixedLVariation F T a b p) :
    IsLocalMin (variationSquareAction V.toLVariation) 0 := by
  have hzero : (0 : ℝ) ∈ V.toLVariation.parameterDomain :=
    ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hbase : variationLLength V.toLVariation 0 = backwardLLength F T a b p.curve := by
    have hcurve : (fun t ↦ V.family t 0) = p.curve := funext V.at_zero
    simp only [variationLLength, hcurve]
  change ∀ᶠ u in 𝓝 (0 : ℝ),
    variationSquareAction V.toLVariation 0 ≤ variationSquareAction V.toLVariation u
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with u hu
  rw [variationSquareAction_eq_variationLLength V.toLVariation hzero,
    variationSquareAction_eq_variationLLength V.toLVariation hu, hbase]
  exact hmin (variationPath V.toLVariation hu) (V.fixed_left u hu)

theorem hasDerivAt_variationSquareAction_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (hmin : ∀ q : BackwardTimePath F T a b, q.curve a = p.curve a →
      backwardLLength F T a b p.curve ≤ backwardLLength F T a b q.curve)
    (V : InitialFixedLVariation F T a b p) {d : ℝ}
    (hd : HasDerivAt (variationSquareAction V.toLVariation) d 0) : d = 0 :=
  (isLocalMin_variationSquareAction hmin V).hasDerivAt_eq_zero hd

theorem deriv_variationSquareAction_eq_zero {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (hmin : ∀ q : BackwardTimePath F T a b, q.curve a = p.curve a →
      backwardLLength F T a b p.curve ≤ backwardLLength F T a b q.curve)
    (V : InitialFixedLVariation F T a b p) :
    deriv (variationSquareAction V.toLVariation) 0 = 0 :=
  (isLocalMin_variationSquareAction hmin V).deriv_eq_zero

theorem secondVariation_nonneg {J : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {p : BackwardTimePath F T a b}
    (hmin : ∀ q : BackwardTimePath F T a b, q.curve a = p.curve a →
      backwardLLength F T a b p.curve ≤ backwardLLength F T a b q.curve)
    (V : InitialFixedLVariation F T a b p) {d q : ℝ}
    (hd : HasDerivAt (variationSquareAction V.toLVariation) d 0)
    (hdd : HasDerivAt (deriv (variationSquareAction V.toLVariation)) q 0) :
    0 ≤ q := by
  have h := ConjugateVariation.deriv_deriv_nonneg_of_isLocalMin
    (isLocalMin_variationSquareAction hmin V) hd.continuousAt
  rwa [hdd.deriv] at h

end PoincareConjecture.ReducedLengthMinimum.Variation

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem secondVariation_nonneg (K : AncientKappaSolution 2 M)
    {τ : ℝ} {p : BackwardTimePath K.flow 0 0 τ}
    (hmin : ∀ q : BackwardTimePath K.flow 0 0 τ, q.curve 0 = p.curve 0 →
      backwardLLength K.flow 0 0 τ p.curve ≤ backwardLLength K.flow 0 0 τ q.curve)
    (V : InitialFixedLVariation K.flow 0 0 τ p) {q : ℝ}
    (hdd : HasDerivAt (deriv (variationSquareAction V.toLVariation)) q 0) :
    0 ≤ q := by
  have hzero : (0 : ℝ) ∈ V.toLVariation.parameterDomain :=
    ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  exact ReducedLengthMinimum.Variation.secondVariation_nonneg hmin V
    (hasDerivAt_variationSquareAction_integral K.regularizedPotential_contMDiff
      V.toLVariation hzero) hdd

end PoincareConjecture.AncientKappaSolution
