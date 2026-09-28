import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeEndTails
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialGraphSide
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphIsotopy
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalPairIsotopy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28





theorem exists_source_fresh_sphere_isotopy_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D0 D : ℝ}
        {E : SameTimeCounterexample.{u} epsilon C A D0 D}
        {S : CounterexampleNeckSegment E} (T : SourceTubeData S),
        epsilon ≤ epsilon0 → ∀ (f : UnitTwoSphere → ℝ),
          (∀ q, |f q| < epsilon⁻¹ / 32) →
          ∀ (N : EpsilonNeck (E.flow.metric E.time)), N.epsilon = epsilon →
            N.center ∈ (T.carrierOpen : Set _) →
            N.center ∉ (T.list.node 0).2.belowGraph_m28 f →
            Disjoint N.carrier
              (closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)) →
            SmoothSphereIsotopicIn (T.carrierOpen : Set _) N.central_sphere
              T.tube.cylinder.middleSphere := by
  obtain ⟨epsilonI, hIpos, _, hisotopy⟩ := exists_buffered_neck_sphere_isotopy_accuracy.{u}
  refine ⟨min epsilonI (1 / 1000), lt_min hIpos (by norm_num), min_le_right _ _, ?_⟩
  intro epsilon C A D0 D E S T hepsilon f hbound N heps hcenter hside hterminal
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (heps ▸ N.epsilon_pos)
  have hcore : N.center ∈ T.coreUnion (3 / 4) := by
    rcases T.subset_coreUnion_end_tails (hepsilon.trans (min_le_right _ _))
        (le_refl (3 / 4 : ℝ)) hcenter with (hcore | hfirst) | hlast
    · exact hcore
    · exfalso
      apply hside
      refine ⟨hfirst.1, ?_⟩
      have hb := (abs_lt.mp (hbound ((T.list.node 0).2.coordinate_inverse N.center).1)).1
      linarith only [hfirst.2.2, hb, hA]
    · exact False.elim (Set.disjoint_left.mp hterminal
        (N.central_sphere_subset N.center_on_central_sphere) (subset_closure hlast.1))
  obtain ⟨i, hi, z, hz, hzc⟩ := mem_iUnion₂.mp hcore
  have hactive : (i : ℤ) ∈ T.list.active := by
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    have := Finset.mem_range.mp hi
    omega
  let P := (T.list.node (i : ℤ)).2
  have hepsP : P.epsilon = epsilon := T.list.node_epsilon hactive
  have hzdom : z.2 ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ := by
    rw [hepsP]
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hcP : N.center ∈ P.carrier := hzc ▸ P.coordinate_map_mem_of_axial z hzdom
  have haxis : |(P.coordinate_inverse N.center).2| ≤ 3 * P.epsilon⁻¹ / 4 := by
    rw [← hzc, P.coordinate_inverse_coordinate_map_of_axial z hzdom, hepsP]
    exact abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨q, hq⟩ : ∃ q : UnitTwoSphere, N.coordinate_map (q, 0) = N.center := by
    simpa only [← N.centralSphere_range, mem_range] using N.center_on_central_sphere
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [heps]
    exact ⟨neg_lt_zero.mpr hA, hA⟩
  have hNP : SmoothSphereIsotopicIn P.carrier N.central_sphere P.central_sphere := by
    rw [← N.centralSphere_range]
    apply hisotopy _ _ P.connection P N
      (hepsP.trans_le (hepsilon.trans (min_le_left _ _)))
      (heps.trans_le (hepsilon.trans (min_le_left _ _))) 0 hzero q
    · rwa [hq]
    · rwa [hq]
  have hPT : P.carrier ⊆ (T.carrierOpen : Set _) := by
    intro x hx
    rw [T.carrier_eq_iUnion_nodes]
    exact mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hactiveT : (i : ℤ) ∈ T.tube.chain.shape.active := by
    rw [T.tube_chain_readout.1]
    exact hactive
  have hPTisotopy : SmoothSphereIsotopicIn (T.carrierOpen : Set _)
      P.central_sphere T.tube.cylinder.middleSphere := by
    change SmoothSphereIsotopicIn T.tube.carrier
      (T.list.node (i : ℤ)).2.central_sphere T.tube.cylinder.middleSphere
    have h := T.tube.central_sphere_isotopy (i : ℤ) hactiveT
    simpa only [T.tube_chain_readout.2] using h
  exact (hNP.mono_m28 hPT).trans hPTisotopy

end PoincareConjecture.M28
