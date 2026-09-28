import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.Overlap.FrontierHeight
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

private theorem subset_region_of_avoids_faces (N : EpsilonNeck g)
    {a b : ℝ} (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    {S : Set M} (hS : IsPreconnected S) (hmeet : (S ∩ N.region a b).Nonempty)
    (hfaces : ∀ q : UnitTwoSphere,
      N.coordinate_map (q, a) ∉ S ∧ N.coordinate_map (q, b) ∉ S) : S ⊆ N.region a b := by
  let K := N.coordinate_map '' (univ ×ˢ Icc a b)
  have hK : IsCompact K := N.isCompact_coordinate_slab ha hb
  have hreg : N.region a b ⊆ K := by
    intro x hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  apply hS.subset_of_closure_inter_subset (N.isOpen_region a b) hmeet
  rintro x ⟨hx, hxS⟩
  obtain ⟨z, hz, rfl⟩ := closure_minimal hreg hK.isClosed hx
  have hzdom : z ∈ N.cylinderDomain :=
    ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hza : a < z.2 := lt_of_le_of_ne hz.2.1 (by
    intro heq
    have hzEq : z = (z.1, a) := Prod.ext rfl heq.symm
    exact (hfaces z.1).1 (hzEq ▸ hxS))
  have hzb : z.2 < b := lt_of_le_of_ne hz.2.2 (by
    intro heq
    have hzEq : z = (z.1, b) := Prod.ext rfl heq
    exact (hfaces z.1).2 (hzEq ▸ hxS))
  refine ⟨N.coordinate_map_mem hzdom, ?_⟩
  simpa only [N.coordinate_inverse_coordinate_map hzdom] using And.intro hza hzb

theorem reciprocal_strip_of_positive_frontier_contact_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (heq : P.epsilon = N.epsilon)
    {x : M} (hxfront : x ∈ frontier N.carrier)
    (hx : x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹))
    (hxP : x ∈ P.central_sphere) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      {y : M | y ∈ P.carrier ∧ -(3 / 40 : ℝ) * N.epsilon⁻¹ < σ * (P.coordinate_inverse y).2 ∧
        σ * (P.coordinate_inverse y).2 < -(13 / 200 : ℝ) * N.epsilon⁻¹} ⊆
          N.region ((51 / 100 : ℝ) * N.epsilon⁻¹) ((99 / 100 : ℝ) * N.epsilon⁻¹) := by
  obtain ⟨σ, hσ, hheight⟩ := N.frontier_transition_height_bounds_of_epsilon_le
    P hN heq hxfront hx hxP
  have hquarter := N.closure_positive_quarter_subset_of_central_sphere_contact_of_epsilon_le
    P hN heq ⟨x, hx, hxP⟩
  let R := N.epsilon⁻¹
  have hR : 0 < R := inv_pos.mpr N.epsilon_pos
  have hRlarge : (200 : ℝ) ≤ R := by
    change 200 ≤ N.epsilon⁻¹
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  let A := (51 / 100 : ℝ) * R
  let B := (99 / 100 : ℝ) * R
  let S : Set M := {y | y ∈ P.carrier ∧ -(3 / 40 : ℝ) * R < σ * (P.coordinate_inverse y).2 ∧
    σ * (P.coordinate_inverse y).2 < -(13 / 200 : ℝ) * R}
  have hA : A ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
    change R / 2 < (51 / 100 : ℝ) * R ∧ (51 / 100 : ℝ) * R < R
    constructor <;> linarith
  have hB : B ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
    change R / 2 < (99 / 100 : ℝ) * R ∧ (99 / 100 : ℝ) * R < R
    constructor <;> linarith
  have hAB : A < B := by dsimp [A, B]; linarith
  have hupperA (q : UnitTwoSphere) :
      σ * (P.coordinate_inverse (N.coordinate_map (q, A))).2 < -(3 / 40 : ℝ) * R := by
    have h := (hheight q A hA).2
    change _ ≤ -(1 / 4 : ℝ) * (R - (51 / 100 : ℝ) * R) + 9 at h
    linarith
  have hlowerB (q : UnitTwoSphere) :
      -(13 / 200 : ℝ) * R < σ * (P.coordinate_inverse (N.coordinate_map (q, B))).2 := by
    have h := (hheight q B hB).1
    change -(3 / 2 : ℝ) * (R - (99 / 100 : ℝ) * R) - 9 ≤ _ at h
    linarith
  have hS : IsPreconnected S := by
    rcases hσ with rfl | rfl
    · have hSe : S = P.region (-(3 / 40 : ℝ) * R) (-(13 / 200 : ℝ) * R) := by
        ext y
        simp only [S, region, mem_ofPred_eq, one_mul]
      rw [hSe]
      apply (P.isConnected_region ?_ ?_ ?_).2
      · rw [heq]; change -R ≤ -(3 / 40 : ℝ) * R; linarith
      · rw [heq]; change -(13 / 200 : ℝ) * R ≤ R; linarith
      · linarith
    · have hSe : S = P.region ((13 / 200 : ℝ) * R) ((3 / 40 : ℝ) * R) := by
        ext y
        simp only [S, region, mem_ofPred_eq, neg_one_mul]
        constructor <;> rintro ⟨hy, h₁, h₂⟩ <;> refine ⟨hy, ?_, ?_⟩ <;> linarith
      rw [hSe]
      apply (P.isConnected_region ?_ ?_ ?_).2
      · rw [heq]; change -R ≤ (13 / 200 : ℝ) * R; linarith
      · rw [heq]; change (3 / 40 : ℝ) * R ≤ R; linarith
      · linarith
  refine ⟨σ, hσ, ?_⟩
  apply N.subset_region_of_avoids_faces
    (by change -R < (51 / 100 : ℝ) * R; linarith) hB.2 hS
  · let q := (N.coordinate_inverse N.center).1
    let f : ℝ → ℝ := fun t => σ * (P.coordinate_inverse (N.coordinate_map (q, t))).2
    have hdom (s : ℝ) (hs : s ∈ Icc A B) : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      exact ⟨by change -R < s; linarith [hA.1, hs.1], hs.2.trans_lt hB.2⟩
    have hmem (s : ℝ) (hs : s ∈ Icc A B) : N.coordinate_map (q, s) ∈ P.carrier := by
      apply hquarter
      apply subset_closure
      have hd : (q, s) ∈ N.cylinderDomain := ⟨mem_univ _, hdom s hs⟩
      refine ⟨N.coordinate_map_mem hd, ?_⟩
      rw [N.coordinate_inverse_coordinate_map hd]
      exact ⟨hA.1.trans_le hs.1, hs.2.trans_lt hB.2⟩
    have hf : ContinuousOn f (Icc A B) := continuousOn_const.mul
      (fun s hs => (P.transition_axis_contDiffAt N q (hdom s hs)
        (hmem s hs)).continuousAt.continuousWithinAt)
    have hfa : f A < -(7 / 100 : ℝ) * R := by
      have h := hupperA q
      change σ * (P.coordinate_inverse (N.coordinate_map (q, A))).2 < _
      linarith
    have hfb : -(7 / 100 : ℝ) * R < f B := by
      have h := hlowerB q
      change _ < σ * (P.coordinate_inverse (N.coordinate_map (q, B))).2
      linarith
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hAB.le hf ⟨hfa.le, hfb.le⟩
    have hAs : A < s := lt_of_le_of_ne hs.1 (by
      intro he
      subst s
      exact hfa.ne hfs)
    have hsB : s < B := lt_of_le_of_ne hs.2 (by
      intro he
      subst s
      exact hfb.ne' hfs)
    refine ⟨N.coordinate_map (q, s), ⟨hmem s hs, ?_, ?_⟩,
      N.coordinate_map_mem ⟨mem_univ _, hdom s hs⟩, ?_⟩
    · change -(3 / 40 : ℝ) * R < f s
      rw [hfs]
      linarith
    · change f s < -(13 / 200 : ℝ) * R
      rw [hfs]
      linarith
    · rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom s hs⟩]
      exact ⟨hAs, hsB⟩
  · intro q
    exact ⟨fun hy => (hupperA q).not_gt hy.2.1,
      fun hy => (hlowerB q).not_gt hy.2.2⟩

theorem shifted_slice_subset_positive_end_of_frontier_contact_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (heq : P.epsilon = N.epsilon)
    {x : M} (hxfront : x ∈ frontier N.carrier)
    (hx : x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹))
    (hxP : x ∈ P.central_sphere) :
    ∃ a : ℝ, |a| = (7 / 100 : ℝ) * N.epsilon⁻¹ ∧
      a ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ ∧
      range (fun q : UnitTwoSphere => P.coordinate_map (q, a)) ⊆
        N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
  obtain ⟨σ, hσ, hsub⟩ := N.reciprocal_strip_of_positive_frontier_contact_of_epsilon_le
    P hN heq hxfront hx hxP
  have hR : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let a := -σ * (7 / 100 : ℝ) * N.epsilon⁻¹
  have ha : a ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ := by
    rw [heq]
    dsimp [a]
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith
  refine ⟨a, ?_, ha, ?_⟩
  · dsimp [a]
    rcases hσ with rfl | rfl <;>
      simp [abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 7 / 100) hR)]
  · rintro y ⟨q, rfl⟩
    have hd : (q, a) ∈ P.cylinderDomain := ⟨mem_univ _, ha⟩
    have hheight : σ * a = -(7 / 100 : ℝ) * N.epsilon⁻¹ := by
      dsimp [a]
      rcases hσ with rfl | rfl <;> ring
    have hy := hsub (show P.coordinate_map (q, a) ∈
        {y | y ∈ P.carrier ∧ -(3 / 40 : ℝ) * N.epsilon⁻¹ < σ * (P.coordinate_inverse y).2 ∧
          σ * (P.coordinate_inverse y).2 < -(13 / 200 : ℝ) * N.epsilon⁻¹} from by
      refine ⟨P.coordinate_map_mem hd, ?_⟩
      rw [P.coordinate_inverse_coordinate_map hd, hheight]
      constructor <;> linarith)
    exact ⟨hy.1, (by linarith : N.epsilon⁻¹ / 2 < (51 / 100 : ℝ) * N.epsilon⁻¹).trans hy.2.1,
      hy.2.2.trans (by linarith)⟩

end PoincareConjecture.EpsilonNeck
