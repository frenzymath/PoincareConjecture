import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic









set_option autoImplicit false

open Set

namespace PoincareConjecture.M60




theorem homotopic_of_continuousOn_interval
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F : ℝ × X → Y} {ε s : ℝ} (hε : 0 < ε) (hs : s ∈ Ioo (-ε) ε)
    (hF : ContinuousOn F (Ioo (-ε) ε ×ˢ univ))
    (h0 : Continuous (fun x => F (0, x))) (h1 : Continuous (fun x => F (s, x))) :
    ContinuousMap.Homotopic (⟨fun x => F (0, x), h0⟩ : ContinuousMap X Y)
      (⟨fun x => F (s, x), h1⟩ : ContinuousMap X Y) := by
  refine ⟨{
    toFun := fun q => F ((q.1 : ℝ) * s, q.2)
    continuous_toFun := ?_
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp }⟩
  apply hF.comp_continuous
    (((continuous_subtype_val.comp continuous_fst).mul_const s).prodMk continuous_snd)
  intro q
  refine ⟨?_, mem_univ q.2⟩
  change (q.1 : ℝ) * s ∈ Ioo (-ε) ε
  have hlow := q.1.property.1
  have hupp := q.1.property.2
  by_cases hsign : 0 ≤ s
  · constructor <;> nlinarith [hs.1, hs.2]
  · constructor <;> nlinarith [hs.1, hs.2]

end PoincareConjecture.M60
