import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Geometry
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Nonempty

/-!
# Maximal old intervals in the spliced flow

An old surgery endpoint or the excluded original terminal time retains the
original maximal-interval curvature blow-up. The new slice identification
preserves its full curvature norm.
Source: Morgan--Tian, Definition 15.8, p. 362.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.Surgery.Splice

variable (F : SurgeryFlowData.{u}) (T : ℝ) (C : GeneralizedSliceCarrier.{u})
  {B : ℝ≥0∞} (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

theorem maximal_intervals_before (I : RepairedContinuationInput F T)
    (a b : ℝ) (ha : 0 ≤ a) (hstart : a = 0 ∨ a ∈ eventTimes F T) (hab : a < b)
    (hfree : Disjoint (eventTimes F T) (Ioo a b))
    (hb : b ∈ F.surgery_times ∨ b = T) :
    ∀ L : ℝ, ∀ s : ℝ, s < b → ∃ t ∈ Ioo (max a s) b,
      ∃ x : (slice F T C R t).carrier, L < (connection F T C R t).curvatureTensorNorm x := by
  have hbT : b ≤ T := by
    rcases hb with hb | rfl
    · exact ((I.time_domain_eq ▸ F.surgery_times_subset hb).2).le
    · exact le_rfl
  have haT : a < T := hab.trans_le hbT
  have haF : a ∈ F.time_domain := I.time_domain_eq ▸ (show a ∈ Ico 0 T from ⟨ha, haT⟩)
  have hstartF : a = 0 ∨ a ∈ F.surgery_times := by
    rcases hstart with hzero | hevent
    · exact Or.inl hzero
    · rcases mem_insert_iff.mp hevent with heq | hold
      · exact (haT.ne heq).elim
      · exact Or.inr hold
  have hJ : Ico a b ⊆ F.time_domain := by
    intro t ht
    rw [I.time_domain_eq]
    exact ⟨ha.trans ht.1, ht.2.trans_le hbT⟩
  have hfreeF := hfree.mono_left (subset_insert T F.surgery_times)
  have hbF : b ∈ F.surgery_times ∨ b ∉ F.time_domain := by
    rcases hb with hold | rfl
    · exact Or.inl hold
    · right
      rw [I.time_domain_eq]
      exact fun h => h.2.false
  let := I.slices_nonempty a haF
  intro L s hs
  obtain ⟨t, ht, x, hL⟩ := F.maximal_intervals a b haF hstartF hab hJ hfreeF hbF L s hs
  have htT : t < T := ht.2.trans_le hbT
  refine ⟨t, ht, identifyBefore F T C R t htT x, ?_⟩
  rw [curvature_before F T C R t htT]
  exact hL

end PoincareMT.Surgery.Splice
