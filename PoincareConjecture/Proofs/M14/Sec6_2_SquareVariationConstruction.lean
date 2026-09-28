import PoincareConjecture.Proofs.M14.Sec6_2_SquareCurve
import PoincareConjecture.Statements.M14PathCalculus

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

noncomputable def backwardFamilyOfSquare (p : M14BackwardPath G T τ₁ τ₂ x y)
    (H : ℝ × ℝ → G.Point) (τ v : ℝ) : G.Point := by
  classical
  exact if τ ∈ Icc τ₁ τ₂ then H (Real.sqrt τ, v) else p.curve τ

variable {p : M14BackwardPath G T τ₁ τ₂ x y}

theorem backwardFamilyOfSquare_eq (H : ℝ × ℝ → G.Point)
    {τ : ℝ} (hτ : τ ∈ Icc τ₁ τ₂) (v : ℝ) :
    backwardFamilyOfSquare p H τ v = H (Real.sqrt τ, v) := by
  simp only [backwardFamilyOfSquare, if_pos hτ]

theorem backwardFamilyOfSquare_square (H : ℝ × ℝ → G.Point)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (v : ℝ) :
    H (s, v) = backwardFamilyOfSquare p H (s ^ 2) v := by
  have hs0 := (Real.sqrt_nonneg τ₁).trans hs.1
  have hτ : s ^ 2 ∈ Icc τ₁ τ₂ := by
    constructor
    · nlinarith [Real.sq_sqrt p.tau_nonneg, Real.sqrt_nonneg τ₁, hs.1]
    · nlinarith [Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), hs.2,
        Real.sqrt_nonneg τ₂]
  rw [backwardFamilyOfSquare_eq H hτ, Real.sqrt_sq hs0]

private theorem square_slice_smooth {H : ℝ × ℝ → G.Point} {P : Set ℝ}
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P)) {v : ℝ} (hv : v ∈ P) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun s => H (s, v))
      (M14SqrtParameterInterval τ₁ τ₂) :=
  hH.comp (contMDiff_id.prodMk (contMDiff_const (c := v))).contMDiffOn
    (fun _ hs => ⟨hs, hv⟩)

theorem backwardFamilyOfSquare_smooth {H : ℝ × ℝ → G.Point} {P : Set ℝ}
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P)) {v : ℝ} (hv : v ∈ P) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞
      (fun τ => backwardFamilyOfSquare p H τ v) (Ioo τ₁ τ₂) :=
  (sqrtPullback_contMDiffOn p.tau_nonneg (square_slice_smooth hH hv)).congr
    (fun _ hτ => backwardFamilyOfSquare_eq H (Ioo_subset_Icc_self hτ) v)

theorem backwardFamilyOfSquare_time {H : ℝ × ℝ → G.Point} {P : Set ℝ}
    (hclock : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v ∈ P,
      G.spacetime.timeFunction (H (s, v)) = T - s ^ 2)
    {τ v : ℝ} (hτ : τ ∈ Icc τ₁ τ₂) (hv : v ∈ P) :
    G.spacetime.timeFunction (backwardFamilyOfSquare p H τ v) = T - τ := by
  rw [backwardFamilyOfSquare_eq H hτ, hclock _
    ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩ v hv,
    Real.sq_sqrt (p.tau_nonneg.trans hτ.1)]

theorem backwardFamilyOfSquare_action_integrable
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {H : ℝ × ℝ → G.Point} {P : Set ℝ}
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P)) {v : ℝ} (hv : v ∈ P) :
    IntervalIntegrable (M14RawLIntegrand G (fun τ => backwardFamilyOfSquare p H τ v)
      (projectedCurveVelocity G (fun τ => backwardFamilyOfSquare p H τ v)))
      MeasureTheory.volume τ₁ τ₂ := by
  have hint := sqrtPullback_action_integrable hM12 p.tau_nonneg p.tau_lt
    (square_slice_smooth hH hv)
  apply hint.congr_uIoo
  intro τ hτ
  rw [uIoo_of_le p.tau_lt.le] at hτ
  apply rawLIntegrand_projectedVelocity_congr
  filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
  exact (backwardFamilyOfSquare_eq H (Ioo_subset_Icc_self ht) v).symm

noncomputable def variationOfSquare (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (R : M14SquareRootPath G p) (H : ℝ × ℝ → G.Point) (r : ℝ) (hr : 0 < r)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ Ioo (-r) r))
    (hclock : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v ∈ Ioo (-r) r,
      G.spacetime.timeFunction (H (s, v)) = T - s ^ 2)
    (hzero : ∀ s, H (s, 0) = R.curve s) : M14LVariationData G p R := by
  classical
  let family := backwardFamilyOfSquare p H
  let velocity := fun v => projectedCurveVelocity G (fun τ => family τ v)
  have hsquare (s : ℝ) (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (v : ℝ) :
      H (s, v) = family (s ^ 2) v := backwardFamilyOfSquare_square H hs v
  refine {
    family := family
    family_velocity := velocity
    family_at_zero := ?_
    radius := r
    radius_pos := hr
    parameterDomain := Ioo (-r) r
    parameterDomain_eq := rfl
    parameterDomain_nonempty := ⟨0, neg_lt_zero.mpr hr, hr⟩
    family_time := fun _ hv _ hτ => backwardFamilyOfSquare_time hclock hτ hv
    family_derivative := ?_
    squareFamily := fun s v => H (s, v)
    squareDomain := M14SqrtParameterInterval τ₁ τ₂ ×ˢ Ioo (-r) r
    square_contains := Subset.rfl
    square_smooth := hH
    square_agrees := fun s hs v _ => hsquare s hs v
    square_base := hzero
    square_horizontal_velocity := fun s v => if hs : s ∈ M14SqrtParameterInterval τ₁ τ₂
      then (hsquare s hs v).symm ▸ ((2 * s) • velocity v (s ^ 2)) else 0
    square_horizontal_agrees := ?_
    left_endpoint_fixed := ∀ v ∈ Ioo (-r) r, family τ₁ v = p.curve τ₁
    left_endpoint_fixed_spec := Iff.rfl
    right_endpoint_fixed := ∀ v ∈ Ioo (-r) r, family τ₂ v = p.curve τ₂
    right_endpoint_fixed_spec := Iff.rfl
    action_integrable := fun _ hv => backwardFamilyOfSquare_action_integrable hM12 hH hv }
  · intro τ
    by_cases hτ : τ ∈ Icc τ₁ τ₂
    · rw [show family τ 0 = H (Real.sqrt τ, 0) from backwardFamilyOfSquare_eq H hτ 0,
        hzero, R.agrees _ ⟨Real.sqrt_le_sqrt hτ.1, Real.sqrt_le_sqrt hτ.2⟩,
        Real.sq_sqrt (p.tau_nonneg.trans hτ.1)]
    · simp only [family, backwardFamilyOfSquare, if_neg hτ]
  · intro v hv τ hτ
    apply projectedCurveVelocity_derivative_eq (T := T)
      (((backwardFamilyOfSquare_smooth hH hv τ hτ).contMDiffAt
        (isOpen_Ioo.mem_nhds hτ)).mdifferentiableAt (by simp))
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
    exact backwardFamilyOfSquare_time hclock (Ioo_subset_Icc_self ht) hv
  · intro s hs v _
    rw [dif_pos hs]

theorem variationOfSquare_bothEndpointsFixed (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (R : M14SquareRootPath G p) (H : ℝ × ℝ → G.Point) (r : ℝ) (hr : 0 < r)
    (hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ Ioo (-r) r))
    (hclock : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v ∈ Ioo (-r) r,
      G.spacetime.timeFunction (H (s, v)) = T - s ^ 2)
    (hzero : ∀ s, H (s, 0) = R.curve s)
    (hleft : ∀ v ∈ Ioo (-r) r, H (Real.sqrt τ₁, v) = p.curve τ₁)
    (hright : ∀ v ∈ Ioo (-r) r, H (Real.sqrt τ₂, v) = p.curve τ₂) :
    M14BothEndpointsFixed (variationOfSquare hM12 R H r hr hH hclock hzero) := by
  constructor
  · intro v hv
    exact (backwardFamilyOfSquare_eq H ⟨le_rfl, p.tau_lt.le⟩ v).trans (hleft v hv)
  · intro v hv
    exact (backwardFamilyOfSquare_eq H ⟨p.tau_lt.le, le_rfl⟩ v).trans (hright v hv)

end PoincareConjecture.M14
