import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetHessian
import PoincareConjecture.Proofs.M14.Sec6_5_GaugeScalarHessian
import PoincareConjecture.Proofs.M14.Sec6_4_VariationGaugeAcceleration
import PoincareConjecture.Proofs.M14.Sec6_4_VariationGaugeDerivative

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

private theorem hessian_pair_eq_of_heq {T τ : ℝ} {q r : G.Point}
    (h : q = r) (hq : G.spacetime.timeFunction q = T - τ)
    (hr : G.spacetime.timeFunction r = T - τ) (f : G.Point → ℝ)
    {Y : G.Horizontal q} {Z : G.Horizontal r} (hY : HEq Y Z) :
    M14ReducedLengthHessianPairing G ⟨q, hq⟩ f Y Y =
      M14ReducedLengthHessianPairing G ⟨r, hr⟩ f Z Z := by
  cases h
  cases hY
  rfl

private theorem scalar_differential_eq_of_heq {q r : G.Point}
    (h : q = r) (f : G.Point → ℝ)
    {Y : G.Horizontal q} {Z : G.Horizontal r} (hY : HEq Y Z) :
    mvfderiv (spacetimeModel n) f q Y.val = mvfderiv (spacetimeModel n) f r Z.val := by
  cases h
  cases hY
  rfl

theorem variationEndpoint_secondDeriv_comp
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b)
    (f : G.Point → ℝ) (O : Set G.Point) (hO : IsOpen O) (hp : R.curve s ∈ O)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ f O) :
    deriv (deriv (fun v => f (V.squareFamily s v))) 0 =
      M14ReducedLengthHessianPairing G ⟨R.curve s, R.curve_time s hs⟩ f
        (M14VariationField V s) (M14VariationField V s) +
      mvfderiv (spacetimeModel n) f (R.curve s)
        (M14VariationEndpointAcceleration V D s hs).val := by
  obtain ⟨j, N, P, β, hN, hsN, hP, hzero, hPsub, hβ, hrec, hclock⟩ :=
    exists_variation_gauge_rectangle V hs
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty j hCoordinates
  let S := M14SqrtParameterInterval a b ∩ N
  have hsS : s ∈ S := ⟨hs, hsN⟩
  let t := (β (s, 0)).1
  let z : ℝ → G.gaugeCover.spatial j := fun v => (β (s, v)).2
  let q : ℝ → EuclideanSpace ℝ (Fin n) := fun v => (z v).val
  let e := (G.gaugeCover.cylinder j).toMovingSpacetimeGauge
  let F : G.gaugeCover.spatial j → G.Point := fun w => e.toSpacetime (t, w)
  let φ : G.gaugeCover.spatial j → ℝ := f ∘ F
  have hF : ContMDiff (𝓡 n) (spacetimeModel n) ∞ F :=
    e.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hbase : F (z 0) = R.curve s := (hrec s hsS 0 hzero).trans (V.square_base s)
  have hz : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ z 0 :=
    ((hβ.comp ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn
      (fun _ hv => ⟨hsS, hv⟩)) 0 hzero).snd.contMDiffAt (hP.mem_nhds hzero)
  have hφ : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ φ (F ⁻¹' O) :=
    hf.comp hF.contMDiffOn (fun _ hw => hw)
  have htarget : z 0 ∈ F ⁻¹' O := by
    change F (z 0) ∈ O
    rwa [hbase]
  have hchain := openSubset_secondDeriv_comp (G.gaugeCover.spatial j) (W.flow.connection t.val)
    φ (F ⁻¹' O) (hO.preimage hF.continuous) hφ z hz htarget
  have htime (r : ℝ) (hr : r ∈ S) : T - r ^ 2 ∈ (G.gaugeCover.interval j).domain := by
    rw [← hclock r hr 0 hzero]
    exact (β (r, 0)).1.property
  let Γ := M08.closedChartConnection W.flow T (z 0) S (s, q 0)
  have hc : (show EuclideanSpace ℝ (Fin n) from
      (W.flow.connection t.val).connection (fun _ => deriv q 0) (z 0) (deriv q 0)) =
        Γ (deriv q 0) (deriv q 0) := by
    rw [show t.val = T - s ^ 2 from hclock s hsS 0 hzero]
    exact openSubset_chartConnection (G.gaugeCover.spatial j) W.flow T htime (z 0) (z 0)
      hsS (deriv q 0) (deriv q 0)
  have hf0 : ContMDiffAt (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ f (F (z 0)) :=
    hf.contMDiffAt (hO.mem_nhds htarget)
  have hH := movingGauge_spacetimeHessian (ordinaryGauge_movingCalculus j hCoordinates W)
    t (z 0) (hclock s hsS 0 hzero) f hf0 (deriv q 0) (deriv q 0)
  have hdf := movingGauge_spacetimeDifferential
    (g := ordinaryGaugeGeometry j W) t (z 0) f hf0
      (deriv (deriv q) 0 + Γ (deriv q 0) (deriv q 0))
  have hY := variationField_gauge V j hP hzero hβ hrec hsS
  have hA := variationEndpointAcceleration_gauge V D j hCoordinates W (z 0)
    inter_subset_left hP hzero hPsub hβ hrec hclock hsS
  have hnear : (fun v => f (V.squareFamily s v)) =ᶠ[𝓝 0] (fun v => φ (z v)) := by
    filter_upwards [hP.mem_nhds hzero] with v hv
    have ht : (β (s, v)).1 = t := Subtype.ext
      ((hclock s hsS v hv).trans (hclock s hsS 0 hzero).symm)
    rw [← hrec s hsS v hv]
    change f (e.toSpacetime ((β (s, v)).1, (β (s, v)).2)) = _
    rw [ht]
    rfl
  rw [hnear.deriv.deriv_eq]
  change deriv (deriv (fun v => φ (z v))) 0 = _
  change deriv (deriv (fun v => φ (z v))) 0 =
    (W.flow.connection t.val).hessian φ (z 0) (deriv q 0) (deriv q 0) +
      mvfderiv (𝓡 n) φ (z 0) (deriv (deriv q) 0 +
        (show EuclideanSpace ℝ (Fin n) from
          (W.flow.connection t.val).connection (fun _ => deriv q 0) (z 0) (deriv q 0))) at hchain
  rw [hc] at hchain
  exact hchain.trans ((congrArg₂ (· + ·) hH hdf).trans (congrArg₂ (· + ·)
    (hessian_pair_eq_of_heq hbase _ _ f hY.symm)
    (scalar_differential_eq_of_heq hbase f hA.symm)))

end PoincareConjecture.M14
