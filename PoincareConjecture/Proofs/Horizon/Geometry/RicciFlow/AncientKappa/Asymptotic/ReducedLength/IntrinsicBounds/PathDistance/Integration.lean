import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.PathDistance.Slope
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.MovingEndpoints.Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

open ReducedLengthBounds

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem regular_paths_distance_increment_le
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z W : TangentSpace (𝓡 n) p} {τ a A : ℝ}
    (hZ : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hW : (W, τ) ∈ G.toLExponentialFamily.regularDomain)
    (ha : 0 < a) (haτ : a ≤ τ) (hA : 1 ≤ A)
    (hendZ : reducedLength K.flow 0 p (G.gamma Z τ) τ ≤ A)
    (hendW : reducedLength K.flow 0 p (G.gamma W τ) τ ≤ A) :
    ((K.flow.metric (-τ)).edist (G.gamma Z τ) (G.gamma W τ)).toReal ≤
      ((K.flow.metric (-a)).edist (G.gamma Z a) (G.gamma W a)).toReal +
        (2 * (n : ℝ) + 604) * (4 * Real.sqrt (A * Real.sqrt τ) *
          (Real.sqrt (Real.sqrt τ) - Real.sqrt (Real.sqrt a))) := by
  have hτ := hZ.1.choose
  have hR := hZ.1.choose_spec.choose
  have hcont (V : TangentSpace (𝓡 n) p) : ContinuousOn (G.gamma V) (Icc a τ) := by
    have h := (G.path V τ hτ hR).continuous
    rw [G.path_eq] at h
    exact h.mono (fun s hs => ⟨ha.le.trans hs.1, hs.2⟩)
  have hJ : Icc (-τ) (-a) ⊆ interior (Iic (0 : ℝ)) := by
    intro t ht
    rw [interior_Iic]
    exact ht.2.trans_lt (neg_neg_of_pos ha)
  have hRic (t : ℝ) (ht : t ∈ Icc (-τ) (-a)) (x : M) (v : TangentSpace (𝓡 n) x) :
      0 ≤ (K.flow.connection t).ricci x v v :=
    ((K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (K.flow.connection t).intrinsicCurvatureTensorCalculus x
      (K.nonnegative_curvature_operator t (ht.2.trans (by linarith)) x) v).1
  let f : ℝ → ℝ := fun s => ((K.flow.metric (-s)).edist (G.gamma Z s) (G.gamma W s)).toReal
  have hf : ContinuousOn f (Icc a τ) := K.flow.continuousOn_backward_moving_distance
    hJ (K.complete (-a) (by linarith)) hRic (hcont Z) (hcont W)
  let C := 2 * (n : ℝ) + 604
  let V : ℝ → ℝ := fun s => 4 * Real.sqrt (A * Real.sqrt τ) * Real.sqrt (Real.sqrt s)
  let B : ℝ → ℝ := fun s => f a + C * (V s - V a)
  have hder (s : ℝ) (hs : s ∈ Icc a τ) :
      HasDerivAt B (C * pathDistanceScale A τ s) s :=
    (((hasDerivAt_fourthRootScale (ha.trans_le hs.1)).sub_const (V a)).const_mul C).const_add (f a)
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (B := B) (B' := fun s => C * pathDistanceScale A τ s)
    (by simp [B])
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hder s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs r hr => (P.regular_paths_eventually_distance_slope_lt G hZ hW
      (ha.trans_le hs.1) hs.2.le hA hendZ hendW hr).frequently)
    (show τ ∈ Icc a τ from ⟨haτ, le_rfl⟩)
  convert! hbound using 1
  dsimp only [f, B, C, V]
  ring

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
