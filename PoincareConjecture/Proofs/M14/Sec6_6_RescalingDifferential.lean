import PoincareConjecture.Proofs.M14.Sec6_6_RescalingExponential
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialLineKernel

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

noncomputable def rescalingHorizontalAt
    (S : GeneralizedFlowSpacetime n X time I) (p q : S.Point) (h : q = p) :
    S.Horizontal p ≃L[ℝ] (M13.parabolicSpacetime S Q hQ a).Horizontal q := by
  subst q
  exact M13.parabolicSpacetimeHorizontal S Q hQ a p

theorem rescalingHorizontalAt_val
    (S : GeneralizedFlowSpacetime n X time I) (p q : S.Point) (h : q = p) (v : S.Horizontal p) :
    (show SpacetimeModelVector n from (rescalingHorizontalAt Q hQ a S p q h v).val) = v.val := by
  subst q
  rfl

theorem rescalingHorizontalAt_metric
    (S : GeneralizedFlowSpacetime n X time I) (p q : S.Point) (h : q = p)
    (v w : S.Horizontal p) :
    (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner q
      (rescalingHorizontalAt Q hQ a S p q h v) (rescalingHorizontalAt Q hQ a S p q h w) =
      Q * S.horizontalMetric.inner p v w := by
  subst q
  exact M13.parabolicSpacetime_metric S Q hQ a p v w

include hCoordinates in

theorem rescalingDifferential_val {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z W : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain)
    (hs' : (rescalingInitialEquiv G.spacetime Q hQ a x Z, Real.sqrt Q * s) ∈ E'.domain) :
    (show SpacetimeModelVector n from
      (E'.differential (rescalingInitialEquiv G.spacetime Q hQ a x Z)
        (Real.sqrt Q * s) hs' (rescalingInitialEquiv G.spacetime Q hQ a x W)).val) =
      (E.differential Z s hs W).val := by
  let A := rescalingInitialEquiv G.spacetime Q hQ a x
  have hline : Continuous (fun r : ℝ => Z + r • W) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hU := (exponentialFamily_domain_slice_isOpen E s).preimage hline
  have hzero : (0 : ℝ) ∈ (fun r : ℝ => Z + r • W) ⁻¹' {V | (V, s) ∈ E.domain} := by
    simpa only [mem_preimage, mem_ofPred_eq, zero_smul, add_zero] using hs
  have hlocal : (fun r : ℝ => E'.gamma (A Z + r • A W) (Real.sqrt Q * s)) =ᶠ[𝓝 0]
      (fun r : ℝ => E.gamma (Z + r • W) s) := by
    filter_upwards [hU.mem_nhds hzero] with r hr
    rw [← map_smul, ← map_add]
    exact rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E E' (Z + r • W) s hr
  have hderiv := congrArg (fun L => L (1 : ℝ))
    (hlocal.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n))
  erw [exponentialLine_mfderiv E' (A Z) (A W) hs', exponentialLine_mfderiv E Z W hs] at hderiv
  exact hderiv

theorem rescalingDifferential_comp {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain)
    (hs' : (rescalingInitialEquiv G.spacetime Q hQ a x Z, Real.sqrt Q * s) ∈ E'.domain) :
    (E'.differential (rescalingInitialEquiv G.spacetime Q hQ a x Z) (Real.sqrt Q * s) hs').comp
        (rescalingInitialEquiv G.spacetime Q hQ a x).toContinuousLinearMap =
      (rescalingHorizontalAt Q hQ a G.spacetime (E.gamma Z s)
        (E'.gamma (rescalingInitialEquiv G.spacetime Q hQ a x Z) (Real.sqrt Q * s))
        (rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a
          E E' Z s hs)).toContinuousLinearMap.comp
          (E.differential Z s hs) := by
  apply ContinuousLinearMap.ext
  intro W
  apply Subtype.ext
  exact (rescalingDifferential_val hCoordinates hM12 hM13 G Q hQ a E E' Z W s hs hs').trans
    (rescalingHorizontalAt_val Q hQ a G.spacetime _ _ _ (E.differential Z s hs W)).symm

include hCoordinates in

theorem rescalingDifferential_bijective_iff {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain)
    (hs' : (rescalingInitialEquiv G.spacetime Q hQ a x Z, Real.sqrt Q * s) ∈ E'.domain) :
    Function.Bijective (E'.differential (rescalingInitialEquiv G.spacetime Q hQ a x Z)
      (Real.sqrt Q * s) hs') ↔ Function.Bijective (E.differential Z s hs) := by
  let A := rescalingInitialEquiv G.spacetime Q hQ a x
  let B := rescalingHorizontalAt Q hQ a G.spacetime (E.gamma Z s)
    (E'.gamma (A Z) (Real.sqrt Q * s))
    (rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E E' Z s hs)
  have hcomp := rescalingDifferential_comp hCoordinates hM12 hM13 G Q hQ a E E' Z s hs hs'
  calc
    _ ↔ Function.Bijective ((E'.differential (A Z) (Real.sqrt Q * s) hs').comp
        A.toContinuousLinearMap) :=
      (Function.Bijective.of_comp_iff _ A.bijective).symm
    _ ↔ Function.Bijective (B.toContinuousLinearMap.comp (E.differential Z s hs)) := by
      rw [hcomp]
      rfl
    _ ↔ _ := Function.Bijective.of_comp_iff' B.bijective _

end PoincareConjecture.M14
