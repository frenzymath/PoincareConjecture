import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.PuncturedBallSimplyConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Simply connected chart-puncture neighborhoods with compact complements

Small balls in one actual chart give a neighborhood basis
whose punctures are simply connected. Compact closed-ball
images control their closures. On a compact Hausdorff space,
the complements are compact and contain any prescribed compact
puncture-avoiding core in their interiors. No PL submanifold
or boundary sphere is asserted. See Hamilton1976 p.66 and
M76 derivation270, the topological end hypothesis.
-/

set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

/-- An actual Euclidean chart in dimension greater than two
has arbitrarily small open neighborhoods with simply connected
punctures. Their whole closures stay in the prescribed open
neighborhood by a compact closed-ball image.
See Hamilton p.66 and M76 derivation270. -/
theorem exists_simplyConnected_punctured_neighborhood
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (hdim : 2 < Module.finrank ℝ E) (Q : OpenPartialHomeomorph E X)
    (h0 : (0 : E) ∈ Q.source) {W : Set X} (hW : IsOpen W) (hW0 : Q 0 ∈ W) :
    ∃ V : Set X, IsOpen V ∧ Q 0 ∈ V ∧ closure V ⊆ W ∧
      IsCompact (closure V) ∧ IsSimplyConnected (V \ {Q 0}) := by
  have hD : IsOpen (Q.source ∩ Q ⁻¹' W) :=
    Q.continuousOn_toFun.isOpen_inter_preimage Q.open_source hW
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD 0 ⟨h0, hW0⟩
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have hclosed : closedBall (0 : E) r ⊆ Q.source ∩ Q ⁻¹' W :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεD
  have hball : ball (0 : E) r ⊆ Q.source :=
    ball_subset_closedBall.trans (hclosed.trans inter_subset_left)
  let V := Q '' ball (0 : E) r
  let C := Q '' closedBall (0 : E) r
  have hC : IsCompact C := (isCompact_closedBall (0 : E) r).image_of_continuousOn
    (Q.continuousOn_toFun.mono (hclosed.trans inter_subset_left))
  have hVC : closure V ⊆ C :=
    closure_minimal (image_mono ball_subset_closedBall) hC.isClosed
  refine ⟨V, Q.isOpen_image_of_subset_source isOpen_ball hball,
    ⟨0, mem_ball_self hr, rfl⟩, ?_, hC.of_isClosed_subset isClosed_closure hVC, ?_⟩
  · rintro x hx
    obtain ⟨z, hz, rfl⟩ := hVC hx
    exact (hclosed hz).2
  · change IsSimplyConnected ((Q '' ball (0 : E) r) \ {Q 0})
    rw [← Q.image_sdiff_singleton_of_subset_source hball h0]
    exact Q.isSimplyConnected_image_of_subset_source (sdiff_subset.trans hball)
      (isSimplyConnected_ball_sdiff_center_of_two_lt_finrank hdim 0 hr)

/-- In a compact Hausdorff space, an actual chart puncture
has a compact complement containing every prescribed compact
core in its interior, while the punctured complement is
simply connected. The compact set is not asserted to be a
PL submanifold. See Hamilton p.66 and M76 derivation270. -/
theorem exists_compact_core_simplyConnected_punctured_complement
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (hdim : 2 < Module.finrank ℝ E) (Q : OpenPartialHomeomorph E X)
    (h0 : (0 : E) ∈ Q.source) {A : Set X} (hA : IsCompact A) (hqA : Q 0 ∉ A) :
    ∃ K : Set X, IsCompact K ∧ A ⊆ interior K ∧ Q 0 ∉ K ∧
      IsSimplyConnected (Kᶜ \ {Q 0}) := by
  obtain ⟨V, hV, hqV, hVA, _, hsc⟩ :=
    Q.exists_simplyConnected_punctured_neighborhood hdim h0 hA.isClosed.isOpen_compl hqA
  refine ⟨Vᶜ, hV.isClosed_compl.isCompact, ?_, ?_, ?_⟩
  · rw [interior_compl]
    intro x hx hxV
    exact hVA hxV hx
  · exact fun hq => hq hqV
  · simpa only [compl_compl] using hsc

end OpenPartialHomeomorph
