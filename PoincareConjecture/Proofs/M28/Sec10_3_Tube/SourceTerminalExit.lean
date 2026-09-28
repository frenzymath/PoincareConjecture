import PoincareConjecture.Proofs.M28.Mathlib.FrontierCrossing
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeData










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
  {S : CounterexampleNeckSegment E}





theorem exists_source_neck_forward_exit
    (T : SourceTubeData S) {i : ℤ} (_hi : i ∈ T.chain.shape.active)
    {a : ℝ} (ha : a ∈ Icc S.lower S.upper)
    (hpath : MapsTo S.path (Icc a S.upper) (T.chain.neck i).carrier)
    (hend : S.path 1 ∉ closure (T.chain.neck i).carrier) :
    ∃ v ∈ Ioo a 1, S.path v ∈ frontier (T.chain.neck i).carrier ∧
      MapsTo S.path (Ico a v) (T.chain.neck i).carrier := by
  have haa : a < 1 := lt_of_le_of_lt ha.2 S.upper_lt_one
  have hstart : S.path a ∈ (T.chain.neck i).carrier :=
    hpath (left_mem_Icc.mpr ha.2)
  have hγ : ContinuousOn S.path (Icc a 1) :=
    S.path_smooth.continuousOn.mono
      (Icc_subset_Icc (S.lower_pos.le.trans ha.1) le_rfl)
  obtain ⟨v, hv, hvfront, hvpath⟩ :=
    ContinuousOn.exists_first_frontier_before_endpoint
      (T.chain.neck i).carrier_open haa hγ hstart hend
  refine ⟨v, hv, hvfront, ?_⟩
  intro t ht
  by_cases htu : t ≤ S.upper
  · exact hpath ⟨ht.1, htu⟩
  · exact hvpath ht

end PoincareConjecture.M28
