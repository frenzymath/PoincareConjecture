import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeVolume











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28




theorem SourceTubeData.node_last_readout
    {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    {S : CounterexampleNeckSegment E} (T : SourceTubeData S) :
    T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ) =
        T.list.nodes.getLast T.list.nonempty ∧
      S.path S.upper ∈
        (T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier := by
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  have hlast : ((T.list.nodes.length - 1 : ℕ) : ℤ) ∈ T.list.active := by
    change 0 ≤ ((T.list.nodes.length - 1 : ℕ) : ℤ) ∧
      ((T.list.nodes.length - 1 : ℕ) : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    omega
  have heq : T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ) =
      T.list.nodes.getLast T.list.nonempty := by
    rw [T.list.node_eq_getElem hlast]
    simpa only [Int.toNat_natCast] using (List.getLast_eq_getElem T.list.nonempty).symm
  refine ⟨heq, ?_⟩
  rw [heq]
  exact T.list.terminal (right_mem_Icc.mpr
    ((T.list.vertex _ (List.getLast_mem T.list.nonempty)).1.2))

namespace CounterexampleNeckFamily




theorem exists_source_terminal_neck_scalar_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)), epsilon ≤ epsilon₀ →
        ∀ B : ℝ, ∀ᶠ k in atTop,
          ∀ x ∈ ((T k).list.node (((T k).list.nodes.length - 1 : ℕ) : ℤ)).2.carrier,
            B < (H.normalizedSliceConnection k).scalarCurvature x := by
  obtain ⟨epsilon₀, hpos, hsmall, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon B
  filter_upwards [H.normalizedSlice_upper_scalar_tendsto.eventually
    (eventually_gt_atTop (2 * B))] with k hk
  intro x hx
  have hlen : 0 < (T k).list.nodes.length := List.length_pos_iff.mpr (T k).list.nonempty
  have hlast : (((T k).list.nodes.length - 1 : ℕ) : ℤ) ∈ (T k).list.active := by
    change 0 ≤ (((T k).list.nodes.length - 1 : ℕ) : ℤ) ∧
      (((T k).list.nodes.length - 1 : ℕ) : ℤ) ≤ ((T k).list.nodes.length : ℤ) - 1
    omega
  let N := ((T k).list.node (((T k).list.nodes.length - 1 : ℕ) : ℤ)).2
  have hepsN : N.epsilon ≤ epsilon₀ :=
    ((T k).list.node_epsilon hlast).trans_le hepsilon
  have hraw := hratio _ _ ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
    N hepsN ((H.segment k).path (H.segment k).upper) (T k).node_last_readout.2 x hx
  have hnormalized : (H.normalizedSliceConnection k).scalarCurvature
      ((H.segment k).path (H.segment k).upper) ≤
        2 * (H.normalizedSliceConnection k).scalarCurvature x := by
    rw [H.normalizedSlice_scalar_eq, H.normalizedSlice_scalar_eq, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hraw (H.base_scalar_pos k).le
  linarith only [hk, hnormalized]




theorem exists_source_terminal_neck_exclusion_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)), epsilon ≤ epsilon₀ →
        ∀ (phi : ℕ → ℕ), StrictMono phi →
        ∀ (J : ∀ k, EpsilonNeck
          ((E (phi k + H.shift)).flow.metric (E (phi k + H.shift)).time)),
          (∀ k, (J k).epsilon = epsilon) → ∀ B : ℝ,
          (∀ᶠ k in atTop, (H.normalizedSliceConnection (phi k)).scalarCurvature
            (J k).center ≤ B) →
          ∀ᶠ k in atTop, Disjoint (J k).carrier
            (closure (((T (phi k)).list.node
              (((T (phi k)).list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)) := by
  obtain ⟨epsilonT, hTpos, hTsmall, hterminal⟩ :=
    exists_source_terminal_neck_scalar_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨min epsilonT epsilonR, lt_min hTpos hRpos,
    (min_le_left _ _).trans hTsmall, ?_⟩
  intro epsilon C A E H T hepsilon phi hphi J hepsJ B hcenter
  have hhigh := hphi.tendsto_atTop.eventually
    (hterminal H T (hepsilon.trans (min_le_left _ _)) (2 * B))
  filter_upwards [hhigh, hcenter] with k hk hcenterK
  apply Disjoint.closure_right _ (J k).carrier_open
  apply disjoint_left.mpr
  intro x hxJ hxLast
  have heps : (J k).epsilon ≤ epsilonR := by
    rw [hepsJ]
    exact hepsilon.trans (min_le_right _ _)
  have hraw := hratio _ _
    ((E (phi k + H.shift)).flow.connection (E (phi k + H.shift)).time)
    (J k) heps x hxJ (J k).center
    ((J k).central_sphere_subset (J k).center_on_central_sphere)
  have hnormalized : (H.normalizedSliceConnection (phi k)).scalarCurvature x ≤
      2 * (H.normalizedSliceConnection (phi k)).scalarCurvature (J k).center := by
    rw [H.normalizedSlice_scalar_eq, H.normalizedSlice_scalar_eq, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hraw (H.base_scalar_pos (phi k)).le
  have hpoint := hk x hxLast
  linarith only [hpoint, hnormalized, hcenterK]

end CounterexampleNeckFamily

end PoincareConjecture.M28
