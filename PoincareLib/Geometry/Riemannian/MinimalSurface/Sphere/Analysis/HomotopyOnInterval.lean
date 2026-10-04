import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic

/-!
# Homotopies from continuous families on real intervals

Morgan-Tian Lemma 18.10, printed pp. 424-426. A continuous variation on
a symmetric open interval connects its central map to every included
slice by restricting to the real segment, in either time direction.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M60

/-- Restriction along the straight time segment gives a genuine homotopy
between the center and any included slice. Source: MT Lemma 18.10,
pp. 424-426, preserving the non-null competitor class. -/
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

end PoincareMT.M60
