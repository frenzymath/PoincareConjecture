import PoincareConjecture.Proofs.M44.Mathlib.FiniteEventInduction
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalStopping
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Algebra.Order.Group.OrderIso











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44




theorem cylinder_forward_eq_of_initial
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale b : ℝ} {I J : Set ℝ} {U V : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : SurgeryFlowCylinder F C origin scale J V)
    (hb : 0 ≤ b) (hI : Icc 0 b ⊆ I) (hJ : Icc 0 b ⊆ J)
    (x : C.carrier) (hx : x ∈ U) (hy : x ∈ V)
    (hinit : e.forward 0 (hI ⟨le_rfl, hb⟩) x =
      f.forward 0 (hJ ⟨le_rfl, hb⟩) x) :
    e.forward b (hI ⟨hb, le_rfl⟩) x = f.forward b (hJ ⟨hb, le_rfl⟩) x := by
  classical
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  have htime (s : ℝ) (hs : s ∈ Icc 0 b) : clock s ∈ F.time_domain :=
    e.time_subset (mem_image_of_mem _ (hI hs))
  have hphysical : Icc (clock 0) (clock b) ⊆ F.time_domain :=
    F.time_domain_interval.out (htime 0 ⟨le_rfl, hb⟩) (htime b ⟨hb, le_rfl⟩)
  let events := clock ⁻¹' F.surgery_times ∩ Ioc 0 b
  have hfinite : events.Finite := by
    apply ((F.surgery_times_finite_on_compact isCompact_Icc hphysical).preimage
      clock.injective.injOn).subset
    intro s hs
    exact ⟨hs.1, clock.monotone hs.2.1.le, clock.monotone hs.2.2⟩
  let Q (s : ℝ) := ∀ hs : s ∈ Icc 0 b,
    e.forward s (hI hs) x = f.forward s (hJ hs) x
  have hQ0 : Q 0 := fun _ => hinit
  have hregular : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, s < t →
      Disjoint (hfinite.toFinset : Set ℝ) (Ioc s t) → Q s → Q t := by
    intro s hs t ht hst hfree hQs htQ
    have hK : Icc (clock s) (clock t) ⊆ F.time_domain :=
      F.time_domain_interval.out (htime s hs) (htime t ht)
    have hNo : Disjoint F.surgery_times (Ioc (clock s) (clock t)) := by
      apply Set.disjoint_left.mpr
      intro T hT hTI
      have hsT : s < clock.symm T := by
        apply clock.strictMono.lt_iff_lt.mp
        simpa only [OrderIso.apply_symm_apply] using hTI.1
      have hTt : clock.symm T ≤ t := by
        apply clock.le_iff_le.mp
        simpa only [OrderIso.apply_symm_apply] using hTI.2
      have hmem : clock.symm T ∈ hfinite.toFinset := by
        apply hfinite.mem_toFinset.mpr
        exact ⟨by simpa only [mem_preimage, OrderIso.apply_symm_apply] using hT,
          hs.1.trans_lt hsT, hTt.trans ht.2⟩
      exact Set.disjoint_left.mp hfree hmem ⟨hsT, hTt⟩
    have h1 := e.slab_compatibility (clock s) (clock t) (clock.strictMono hst) hK hNo
      s (hI hs) t (hI htQ) ⟨le_rfl, (clock.strictMono hst).le⟩
      ⟨(clock.strictMono hst).le, le_rfl⟩ x hx
    have h2 := f.slab_compatibility (clock s) (clock t) (clock.strictMono hst) hK hNo
      s (hJ hs) t (hJ htQ) ⟨le_rfl, (clock.strictMono hst).le⟩
      ⟨(clock.strictMono hst).le, le_rfl⟩ x hy
    rw [hQs hs] at h1
    exact h1.symm.trans h2
  have hevent : ∀ t ∈ hfinite.toFinset, (∀ s ∈ Ico 0 t, Q s) → Q t := by
    intro t ht hprev htQ
    have htE := hfinite.mem_toFinset.mp ht
    have hT : origin + t / scale ∈ F.surgery_times := htE.1
    let : Nonempty (F.slice (origin + t / scale)).carrier := ⟨e.forward t (hI htQ) x⟩
    obtain ⟨r, hr, hr'⟩ := exists_preterminal_parameter e.scale_pos htE.2.1
      (F.event (origin + t / scale) hT).tMinus_lt
    have hrI : r ∈ Icc 0 b := ⟨hr.1, hr.2.le.trans htQ.2⟩
    have h1 := e.surgery_compatibility t (hI htQ) hT r (hI hrI) hr' x hx
    have h2 := f.surgery_compatibility t (hJ htQ) hT r (hJ hrI) hr' x hy
    rw [hprev r hr hrI] at h1
    exact h1.symm.trans h2
  have hall := Poincare.finite_event_induction hfinite.toFinset
    (fun _ hs => (hfinite.mem_toFinset.mp hs).2) Q hQ0 hregular hevent
  exact hall b ⟨hb, le_rfl⟩ ⟨hb, le_rfl⟩

end PoincareConjecture.M44
