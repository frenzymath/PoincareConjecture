import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.BallClosure
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.BallSupremum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M]

theorem continuousAt_sSup_ball (g : RiemannianMetric n M)
    (f : M → ℝ) (hf : Continuous f) (p : M)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    ContinuousAt (fun s : ℝ => sSup (f '' g.ball p s)) r := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply SingularRegularLimit.continuousAt_sSup_ennreal_sublevel (g.edist p) f
    (continuous_const.edist continuous_id) hf p
    Manifold.riemannianEDist_self hr hrR
  · rwa [g.closure_ball_eq_edist_le p (hr.trans hrR)] at hcompact
  · rw [← g.closure_ball_eq_edist_le p hr]
    exact Subset.rfl

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

theorem continuousAt_scalarCurvatureSupOn_ball (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hD : Continuous D.scalarCurvature) (p : M)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    ContinuousAt (fun s : ℝ => scalarCurvatureSupOn g D (g.ball p s)) r := by
  simpa only [scalarCurvatureSupOn, image_eq_range] using
    g.continuousAt_sSup_ball D.scalarCurvature hD p hr hrR hcompact

theorem exists_scalar_calibrated_radius (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hD : Continuous D.scalarCurvature) (p : M)
    {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hleft : scalarCurvatureSupOn g D (g.ball p a) ≤ a⁻¹ ^ 2)
    (hright : b⁻¹ ^ 2 ≤ scalarCurvatureSupOn g D (g.ball p b)) :
    ∃ r ∈ Icc a b, scalarCurvatureSupOn g D (g.ball p r) = r⁻¹ ^ 2 := by
  have hcont : ContinuousOn
      (fun r : ℝ => scalarCurvatureSupOn g D (g.ball p r) - r⁻¹ ^ 2) (Icc a b) := by
    intro r hr
    have hr0 : 0 < r := ha.trans_le hr.1
    exact ((continuousAt_scalarCurvatureSupOn_ball g D hD p hr0
      (hr.2.trans_lt hbR) hcompact).sub
      ((continuousAt_id.inv₀ (ne_of_gt hr0)).pow 2)).continuousWithinAt
  obtain ⟨r, hr, hcal⟩ := intermediate_value_Icc hab hcont
    (show (0 : ℝ) ∈ Icc
      (scalarCurvatureSupOn g D (g.ball p a) - a⁻¹ ^ 2)
      (scalarCurvatureSupOn g D (g.ball p b) - b⁻¹ ^ 2) from
        ⟨sub_nonpos.mpr hleft, sub_nonneg.mpr hright⟩)
  exact ⟨r, hr, sub_eq_zero.mp hcal⟩

theorem exists_scalar_calibrated_radius_of_sandwich (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hD : Continuous D.scalarCurvature) (p : M)
    {a b R q δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    {S : Set M} (hsmall : g.ball p a ⊆ S) (hlarge : S ⊆ g.ball p b)
    (herror : |q - scalarCurvatureSupOn g D S| ≤ δ)
    (hleft : q + δ ≤ a⁻¹ ^ 2) (hright : b⁻¹ ^ 2 ≤ q - δ) :
    ∃ r ∈ Icc a b, scalarCurvatureSupOn g D (g.ball p r) = r⁻¹ ^ 2 := by
  have hmono {A B : Set M} (hA : A.Nonempty) (hAB : A ⊆ B)
      (hBR : B ⊆ g.ball p R) :
      scalarCurvatureSupOn g D A ≤ scalarCurvatureSupOn g D B := by
    have hbdd : BddAbove (D.scalarCurvature '' B) :=
      (hcompact.image hD).bddAbove.mono
        (image_mono (hBR.trans subset_closure))
    simp only [scalarCurvatureSupOn, ← image_eq_range]
    exact csSup_le_csSup hbdd (hA.image _) (image_mono hAB)
  have hpa : p ∈ g.ball p a := by
    change g.edist p p < ENNReal.ofReal a
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr ha
  have hbR' : g.ball p b ⊆ g.ball p R := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hbR.le)
  have hlow := hmono ⟨p, hpa⟩ hsmall (hlarge.trans hbR')
  have hhigh := hmono ⟨p, hsmall hpa⟩ hlarge hbR'
  obtain ⟨herr₁, herr₂⟩ := abs_sub_le_iff.mp herror
  apply exists_scalar_calibrated_radius g D hD p ha hab hbR hcompact
  · linarith
  · linarith

end PoincareConjecture
