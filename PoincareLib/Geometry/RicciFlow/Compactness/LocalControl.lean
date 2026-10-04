import PoincareLib.Geometry.RicciFlow.Compactness.Subsequence
import PoincareLib.Topology.Order.TimeInterval

/-!
# Local control before pointed extraction

The frozen hypotheses give eventual control separately at each radius. A
single diagonal subsequence makes all earlier integer-radius bounds and
compactness assertions hold at each stage, together with the fixed volume
lower bound. The ordinary product-flow vector field permits identity
spacetime embeddings, so the two-time curvature bound also controls fixed
zero-time cylinders.

This prepares the local inputs to Morgan--Tian, Theorem 3.28, p. 51, and
Proposition 5.14 and Theorem 5.15, pp. 90--92. It does not supply the local Shi
estimate or construct normal charts, a limit carrier, or a limit metric.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

/-- The identity embedding satisfies the frozen vector-field condition. -/
def SmoothSpacetimeEmbedding.refl
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) (domain : Set (ℝ × C.carrier)) :
    SmoothSpacetimeEmbedding F F domain where
  toFun := id
  time_preserving := fun _ _ => rfl
  injective_on := Function.injective_id.injOn
  inverse := id
  left_inverse := fun _ _ => rfl
  right_inverse := fun _ _ => rfl
  smooth_on := by
    let := C.topologicalSpace
    let := C.chartedSpace
    let := C.isManifold
    exact contMDiffOn_id
  smooth_inverse_on := by
    let := C.topologicalSpace
    let := C.chartedSpace
    let := C.isManifold
    exact contMDiffOn_id
  vector_field_compatible := by
    let := C.topologicalSpace
    let := C.chartedSpace
    let := C.isManifold
    intro t x
    simp [F.spacetimeVectorField_spatial_zero, mfderiv_const]

namespace PointedRicciFlowCompactnessHypotheses

/-- The two-time hypothesis controls identity cylinders throughout every
interior time set with a bound independent of that time set. -/
theorem exists_identity_cylinder_control
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k in Filter.atTop,
      ∀ I : Set ℝ, I ⊆ Set.Ioo T' T →
        CurvatureBoundOn (H.sequence.flow k) (H.sequence.flow k) A I
          (SmoothSpacetimeEmbedding.refl (H.sequence.flow k)
            (I ×ˢ (H.sequence.flow k).zeroBall A)) K := by
  obtain ⟨K, hK, hbound⟩ := H.all_time_curvature_control_on_zero_ball A hA
  refine ⟨K, hK, hbound.mono ?_⟩
  intro k hk I hI
  exact ⟨hK, fun t ht x hx => hk t (hI ht) x hx⟩

/-- Uniformize compactness, two-time curvature, and noncollapse on all earlier
integer-radius stages using one strictly increasing subsequence. -/
theorem exists_uniform_local_control
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T) :
    ∃ r₀ κ : ℝ, 0 < r₀ ∧ 0 < κ ∧
      ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k,
          ENNReal.ofReal (κ * r₀ ^ n) ≤ (H.sequence.flow (φ k)).zeroBallVolume r₀ ∧
          ∀ j, j ≤ k →
            let C := H.sequence.carrier (φ k)
            let F := H.sequence.flow (φ k)
            letI : TopologicalSpace C.carrier := C.topologicalSpace
            letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
            letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
            IsCompact (closure (F.zeroBall (j + 1))) ∧
              ∀ t₀ ∈ Set.Ioo T' T, ∀ t ∈ Set.Ioo T' T,
                ∀ x ∈ F.ballAt t₀ (j + 1),
                  (F.flow.connection t).curvatureTensorNorm x ≤ K j := by
  obtain ⟨r₀, κ, hr₀, hκ, hvolume⟩ := H.noncollapsing
  choose K hK hbound using fun j : ℕ =>
    H.all_time_curvature_control (j + 1) (by positivity)
  have hlocal (j : ℕ) :=
    (H.zero_time_ball_compact (j + 1) (by positivity)).and (hbound j)
  obtain ⟨φ, hφ, hstage⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually
      (fun j => hvolume.and (hlocal j))
  exact ⟨r₀, κ, hr₀, hκ, K, hK, φ, hφ, fun k =>
    ⟨(hstage k 0 (Nat.zero_le k)).1, fun j hj => (hstage k j hj).2⟩⟩

/-- The diagonal sequence has compact zero-time balls and controlled identity
cylinders on each compact time window. Both the volume scale and the curvature
constant for a radius are independent of the window. -/
theorem exists_controlled_exhaustion_cylinders
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T) :
    ∃ r₀ κ : ℝ, 0 < r₀ ∧ 0 < κ ∧
      ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k,
          ENNReal.ofReal (κ * r₀ ^ n) ≤ (H.sequence.flow (φ k)).zeroBallVolume r₀ ∧
          ∀ j, j ≤ k →
            (let C := H.sequence.carrier (φ k)
             letI : TopologicalSpace C.carrier := C.topologicalSpace
             IsCompact (closure ((H.sequence.flow (φ k)).zeroBall (j + 1)))) ∧
            ∀ m : ℕ,
              CurvatureBoundOn (H.sequence.flow (φ k)) (H.sequence.flow (φ k))
                (j + 1) (Poincare.TimeInterval.exhaustion T' T m)
                (SmoothSpacetimeEmbedding.refl (H.sequence.flow (φ k))
                  (Poincare.TimeInterval.exhaustion T' T m ×ˢ
                    (H.sequence.flow (φ k)).zeroBall (j + 1))) (K j) := by
  obtain ⟨r₀, κ, hr₀, hκ, K, hK, φ, hφ, hstage⟩ := H.exists_uniform_local_control
  refine ⟨r₀, κ, hr₀, hκ, K, hK, φ, hφ, fun k => ⟨(hstage k).1, ?_⟩⟩
  intro j hj
  obtain ⟨hcompact, hbound⟩ := (hstage k).2 j hj
  refine ⟨hcompact, fun m => ⟨hK j, ?_⟩⟩
  intro t ht x hx
  exact hbound 0 ⟨H.time_bounds.1, H.time_bounds.2⟩ t
    (Poincare.TimeInterval.exhaustion_subset_Ioo H.time_bounds.1 H.time_bounds.2 m ht) x hx

end PointedRicciFlowCompactnessHypotheses

end PoincareMT

