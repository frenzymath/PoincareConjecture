import PoincareConjecture.Proofs.M28.Mathlib.FiniteChartCover
import Mathlib.Data.Countable.Defs

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold Topology

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem IsCompact.exists_finite_buffered_extChart_ball_cover
    {K W : Set M} (hK : IsCompact K)
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ s : Finset M, ∃ r : M → ℝ,
      (∀ q ∈ s, q ∈ K ∧ 0 < r q ∧
        closedBall (extChartAt I q q) (2 * r q) ⊆
          (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' W) ∧
      K ⊆ ⋃ q ∈ s, (extChartAt I q).source ∩
        (extChartAt I q) ⁻¹' ball (extChartAt I q q) (r q) := by
  classical
  have hchoose : ∀ q : M, ∃ r : ℝ, 0 < r ∧
      (q ∈ K → closedBall (extChartAt I q q) (2 * r) ⊆
        (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' W) := by
    intro q
    by_cases hq : q ∈ K
    · have hopen : IsOpen ((extChartAt I q).target ∩
          (extChartAt I q).symm ⁻¹' W) :=
        (continuousOn_extChartAt_symm (I := I) q).isOpen_inter_preimage
          (isOpen_extChartAt_target q) hW
      have hmem : extChartAt I q q ∈ (extChartAt I q).target ∩
          (extChartAt I q).symm ⁻¹' W := by
        refine ⟨mem_extChartAt_target q, ?_⟩
        simpa only [mem_preimage, extChartAt_to_inv] using hKW hq
      obtain ⟨R, hR, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hmem)
      refine ⟨R / 2, half_pos hR, fun _ => ?_⟩
      simpa only [show 2 * (R / 2) = R by ring] using hsub
    · exact ⟨1, zero_lt_one, fun h => (hq h).elim⟩
  choose r hr hinside using hchoose
  let U := fun q : M => (extChartAt I q).source ∩
    (extChartAt I q) ⁻¹' ball (extChartAt I q q) (r q)
  have hopen (q : M) : IsOpen (U q) :=
    (continuousOn_extChartAt (I := I) q).isOpen_inter_preimage
      (isOpen_extChartAt_source q) isOpen_ball
  have hmem (q : M) : q ∈ U q :=
    ⟨mem_extChartAt_source q, mem_ball_self (hr q)⟩
  obtain ⟨s, hsK, hcover⟩ := hK.elim_nhds_subcover U
    (fun q _ => (hopen q).mem_nhds (hmem q))
  exact ⟨s, r, fun q hq => ⟨hsK q hq, hr q, hinside q (hsK q hq)⟩, hcover⟩

theorem IsCompact.exists_nat_buffered_extChart_ball_cover
    {K W : Set M} (hK : IsCompact K) (hne : K.Nonempty)
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ q : ℕ → M, ∃ r : ℕ → ℝ, (range q).Finite ∧
      (∀ i, q i ∈ K ∧ 0 < r i ∧
        closedBall (extChartAt I (q i) (q i)) (2 * r i) ⊆
          (extChartAt I (q i)).target ∩ (extChartAt I (q i)).symm ⁻¹' W) ∧
      K ⊆ ⋃ i, (extChartAt I (q i)).source ∩
        (extChartAt I (q i)) ⁻¹' ball (extChartAt I (q i) (q i)) (r i) := by
  classical
  obtain ⟨s, r, hs, hcover⟩ := hK.exists_finite_buffered_extChart_ball_cover I hW hKW
  obtain ⟨p, hp⟩ := hne
  obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hp)
  obtain ⟨hqs, _⟩ := mem_iUnion.mp hq
  let : Nonempty s := ⟨⟨q, hqs⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat s
  refine ⟨fun i => (e i).val, fun i => r (e i).val, ?_,
    fun i => hs (e i).val (e i).property, ?_⟩
  · exact s.finite_toSet.subset (range_subset_iff.mpr fun i => (e i).property)
  · intro p hp
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hp)
    obtain ⟨hqs, hpq⟩ := mem_iUnion.mp hq
    obtain ⟨i, hi⟩ := he ⟨q, hqs⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    simpa only [hi] using hpq
