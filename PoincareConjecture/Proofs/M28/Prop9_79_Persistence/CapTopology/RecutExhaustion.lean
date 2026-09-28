import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.RecutVolume

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_recut_capturing_compact (N : CapCertificate g)
    {K : Set M} (hK : IsCompact K) (hKN : K ⊆ N.carrier) :
    ∃ q : ℝ, 0 < q ∧ q < N.epsilon⁻¹ ∧
      K ⊆ N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let W := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) 0
  have hW : IsOpen W := N.isOpen_recut (neg_neg_of_pos hA) hA
  have hD : IsCompact (K \ W) := hK.diff hW
  have hDE : K \ W ⊆ N.end_neck.carrier := by
    intro x hx
    by_contra hxE
    apply hx.2
    apply Or.inl
    rw [N.closed_core_eq_complement_end]
    exact ⟨hKN hx.1, hxE⟩
  have hcont : ContinuousOn (fun x => (N.end_neck.coordinate_inverse x).2)
      (K \ W) :=
    (continuous_snd.comp_continuousOn
      N.end_neck.coordinate_inverse_smooth.continuousOn).mono hDE
  have hupper : ∀ x ∈ K \ W,
      (N.end_neck.coordinate_inverse x).2 < N.epsilon⁻¹ := by
    intro x hx
    simpa only [N.end_neck_epsilon] using
      (N.end_neck.coordinate_inverse_mem x (hDE hx)).2.2
  have hbounded : ∃ b : ℝ, b < N.epsilon⁻¹ ∧
      ∀ x ∈ K \ W, (N.end_neck.coordinate_inverse x).2 ≤ b :=
    hD.exists_forall_le' (α := OrderDual ℝ) hcont hupper
  obtain ⟨b, hb, hbound⟩ := hbounded
  obtain ⟨q, hq, hqA⟩ := exists_between (max_lt hA hb)
  have hq0 : 0 < q := (le_max_left _ _).trans_lt hq
  have hbq : (b : ℝ) < q := (le_max_right (0 : ℝ) (b : ℝ)).trans_lt hq
  refine ⟨q, hq0, hqA, ?_⟩
  intro x hx
  by_cases hxW : x ∈ W
  · rcases hxW with hxY | hxE
    · exact Or.inl hxY
    · exact Or.inr ⟨hxE.1, hxE.2.1, hxE.2.2.trans hq0⟩
  · have hxD : x ∈ K \ W := ⟨hx, hxW⟩
    refine Or.inr ⟨hDE hxD, ?_, (hbound x hxD).trans_lt hbq⟩
    simpa only [N.end_neck_epsilon] using
      (N.end_neck.coordinate_inverse_mem x (hDE hxD)).2.1

theorem eventually_subset_recutTarget (N : CapCertificate g)
    {delta : ℕ → ℝ} (hdelta : Tendsto delta atTop (𝓝 0))
    {K : Set M} (hK : IsCompact K) (hKN : K ⊆ N.carrier) :
    ∀ᶠ k in atTop, K ⊆ recutTarget N delta k := by
  obtain ⟨q, _, hqA, hKq⟩ := N.exists_recut_capturing_compact hK hKN
  filter_upwards [hdelta.eventually (gt_mem_nhds (sub_pos.mpr hqA))]
    with k hk
  intro x hx
  rcases hKq hx with hxY | hxE
  · exact Or.inl hxY
  · exact Or.inr ⟨hxE.1, hxE.2.1, by linarith [hxE.2.2]⟩

theorem eventually_core_ball_subset_recutTarget (N : CapCertificate g)
    {delta : ℕ → ℝ} (hdelta : Tendsto delta atTop (𝓝 0))
    {y : M} (hy : y ∈ N.core) :
    ∀ᶠ k in atTop,
      closure (g.ball y (N.core_radius y)) ⊆ recutTarget N delta k :=
  N.eventually_subset_recutTarget hdelta
    (N.core_ball_compact y hy) (N.core_ball_subset y hy)

end PoincareConjecture.CapCertificate
