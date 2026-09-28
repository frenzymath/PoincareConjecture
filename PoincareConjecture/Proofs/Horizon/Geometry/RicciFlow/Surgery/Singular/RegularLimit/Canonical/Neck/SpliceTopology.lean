import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set Topology TopologicalSpace

universe u v

namespace PoincareConjecture.SingularRegularLimit

theorem isEmbedding_of_time_regions
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {sourceTime : X → ℝ} {targetTime : Y → ℝ}
    (hsource : Continuous sourceTime) (htarget : Continuous targetTime)
    (htime : ∀ x, targetTime (f x) = sourceTime x)
    {a b : ℝ} (hab : a < b)
    (hearly : IsEmbedding (fun x : {x : X | sourceTime x < b} => f x))
    (hlate : IsEmbedding (fun x : {x : X | a < sourceTime x} => f x)) :
    IsEmbedding f := by
  have hEarlyOpen : IsOpen {x : X | sourceTime x < b} :=
    isOpen_lt hsource continuous_const
  have hLateOpen : IsOpen {x : X | a < sourceTime x} :=
    isOpen_lt continuous_const hsource
  have hcontinuous : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : sourceTime x < b
    · exact (continuousOn_iff_continuous_domRestrict.mpr hearly.continuous).continuousAt
        (hEarlyOpen.mem_nhds hx)
    · exact (continuousOn_iff_continuous_domRestrict.mpr hlate.continuous).continuousAt
        (hLateOpen.mem_nhds (hab.trans_le (le_of_not_gt hx)))
  let U : Bool → Opens Y := Bool.rec
    ⟨{y | targetTime y < b}, isOpen_lt htarget continuous_const⟩
    ⟨{y | a < targetTime y}, isOpen_lt continuous_const htarget⟩
  let D : Bool → Set X := Bool.rec {x | sourceTime x < b} {x | a < sourceTime x}
  let V : Bool → Type u := fun i => ↥(D i)
  let inclusion (i : Bool) : V i → X := Subtype.val
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f hcontinuous U ?_ V
    inclusion ?_ ?_ ?_
  · rintro y ⟨x, rfl⟩
    change f x ∈ iSup U
    apply Opens.mem_iSup.mpr
    by_cases hx : sourceTime x < b
    · refine ⟨false, ?_⟩
      change targetTime (f x) < b
      rwa [htime]
    · refine ⟨true, ?_⟩
      change a < targetTime (f x)
      rw [htime]
      exact hab.trans_le (le_of_not_gt hx)
  · intro i
    cases i <;> exact continuous_subtype_val
  · intro i x hx
    cases i
    · exact ⟨⟨x, by change targetTime (f x) < b at hx; rwa [htime] at hx⟩, rfl⟩
    · exact ⟨⟨x, by change a < targetTime (f x) at hx; rwa [htime] at hx⟩, rfl⟩
  · intro i
    cases i
    · exact hearly
    · exact hlate

end PoincareConjecture.SingularRegularLimit
