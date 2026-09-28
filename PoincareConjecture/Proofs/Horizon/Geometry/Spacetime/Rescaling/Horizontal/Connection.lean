import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Horizontal.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Horizontal.SliceConnection
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.HorizontalCalculus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem parabolic_leafwise_connection
    (hTarget : ∀ D' : LeafwiseLeviCivitaFamily
      (spacetimeRescaling R Q hQ a).realization.spacetime
      (spacetimeRescaling R Q hQ a).realization.slices, HorizontalRicciCalculus D')
    (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily (spacetimeRescaling R Q hQ a).realization.spacetime
      (spacetimeRescaling R Q hQ a).realization.slices)
    (U : Set R.spacetime.Point) (hU : IsOpen U)
    (V : HorizontalSection R.spacetime) (hV : IsSmoothHorizontalSectionOn R.spacetime V U)
    (p : R.spacetime.Point) (hp : p ∈ U) (v : R.spacetime.Horizontal p) :
    rawLeafwiseCovariantDerivative D' (parabolicHorizontalSection (spacetimeRescaling R Q hQ a) V)
      p ((spacetimeRescaling R Q hQ a).horizontal p v) =
        (spacetimeRescaling R Q hQ a).horizontal p (rawLeafwiseCovariantDerivative D V p v) := by
  let P := spacetimeRescaling R Q hQ a
  let D₀ : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices :=
    parabolicLeafwiseConnection D Q hQ a
  have hchoice := (hTarget D').leafwise_choice D₀ U hU (parabolicHorizontalSection P V)
    ((parabolic_section_smooth_iff V U).2 hV) p hp
  rw [hchoice]
  exact parabolic_leafwise_chosen D Q hQ a V p v

theorem parabolic_horizontal_connection
    (hTarget : ∀ D' : LeafwiseLeviCivitaFamily
      (spacetimeRescaling R Q hQ a).realization.spacetime
      (spacetimeRescaling R Q hQ a).realization.slices, HorizontalRicciCalculus D')
    (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily (spacetimeRescaling R Q hQ a).realization.spacetime
      (spacetimeRescaling R Q hQ a).realization.slices)
    (U : Set R.spacetime.Point) (hU : IsOpen U)
    (V : HorizontalSection R.spacetime) (hV : IsSmoothHorizontalSectionOn R.spacetime V U)
    (p : R.spacetime.Point) (hp : p ∈ U) (Z : TangentSpace (spacetimeModel n) p) :
    rawHorizontalCovariantDerivative D'
      (parabolicHorizontalSection (spacetimeRescaling R Q hQ a) V) p Z =
        (spacetimeRescaling R Q hQ a).horizontal p (rawHorizontalCovariantDerivative D V p Z) := by
  let P := spacetimeRescaling R Q hQ a
  have hfactor (c : ℝ) : (Q * c) * (1 / Q) = c := by field_simp [hQ.ne']
  have htime := P.time_differential p Z
  dsimp only at htime
  unfold rawHorizontalCovariantDerivative
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply]
  erw [P.projection_eq,
    parabolic_leafwise_connection hTarget D D' U hU V hV p hp,
    parabolic_timeBracket, htime]
  simp only [map_add, map_smul, smul_smul, hfactor]
  rfl

end PoincareConjecture.ParabolicRescaling
