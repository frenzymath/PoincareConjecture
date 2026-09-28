import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalIntervals
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_OpenRegularCylinder










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}




theorem cylinder_preterminal_coordinates_eq
    (e : SurgeryFlowCylinder F C origin scale I U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (hfree : Disjoint F.surgery_times (Ioo (F.event T hT).tMinus T))
    (s : ℝ) (hs : s ∈ I) (t : ℝ) (ht : t ∈ I)
    (hs' : origin + s / scale ∈ Ico (F.event T hT).tMinus T)
    (ht' : origin + t / scale ∈ Ico (F.event T hT).tMinus T)
    (x : C.carrier) (hx : x ∈ U) :
    ((F.event T hT).pre_identify ⟨origin + s / scale, hs'⟩).symm
        (e.forward s hs x) =
      ((F.event T hT).pre_identify ⟨origin + t / scale, ht'⟩).symm
        (e.forward t ht x) := by
  let event := F.event T hT
  let b := (max (origin + s / scale) (origin + t / scale) + T) / 2
  have hmax := max_lt hs'.2 ht'.2
  have hsb : origin + s / scale ≤ b := by
    dsimp [b]
    linarith [le_max_left (origin + s / scale) (origin + t / scale)]
  have htb : origin + t / scale ≤ b := by
    dsimp [b]
    linarith [le_max_right (origin + s / scale) (origin + t / scale)]
  have hbT : b < T := by dsimp [b]; linarith
  have hab : event.tMinus < b := by
    dsimp [b]
    linarith [hs'.1, le_max_left (origin + s / scale) (origin + t / scale)]
  have hprefix : Icc 0 T ⊆ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
  have hJ : Icc event.tMinus b ⊆ F.time_domain :=
    fun _ hu => hprefix ⟨event.tMinus_nonnegative.trans hu.1, hu.2.trans hbT.le⟩
  have hS : Disjoint F.surgery_times (Ioc event.tMinus b) :=
    Set.disjoint_left.mpr fun _ hu hv =>
      Set.disjoint_left.mp hfree hu ⟨hv.1, hv.2.trans_lt hbT⟩
  have hsI : origin + s / scale ∈ Icc event.tMinus b := ⟨hs'.1, hsb⟩
  have htI : origin + t / scale ∈ Icc event.tMinus b := ⟨ht'.1, htb⟩
  have hslab := e.slab_compatibility event.tMinus b hab hJ hS
    s hs t ht hsI htI x hx
  have hpre := F.event_slab_compatibility T hT event.tMinus b hab hJ hS
    (origin + s / scale) (origin + t / scale) hsI htI hs' ht'
    (((event.pre_identify ⟨origin + s / scale, hs'⟩).symm) (e.forward s hs x))
  rw [Diffeomorph.apply_symm_apply] at hpre
  rw [hslab] at hpre
  simpa only [event, Diffeomorph.symm_apply_apply] using
    (congrArg (event.pre_identify ⟨origin + t / scale, ht'⟩).symm hpre).symm




theorem cylinder_preterminal_coordinates_eq_of_pinched
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale I U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (s : ℝ) (hs : s ∈ I) (t : ℝ) (ht : t ∈ I)
    (hs' : origin + s / scale ∈ Ico (F.event T hT).tMinus T)
    (ht' : origin + t / scale ∈ Ico (F.event T hT).tMinus T)
    (x : C.carrier) (hx : x ∈ U) :
    ((F.event T hT).pre_identify ⟨origin + s / scale, hs'⟩).symm
        (e.forward s hs x) =
      ((F.event T hT).pre_identify ⟨origin + t / scale, ht'⟩).symm
        (e.forward t ht x) :=
  cylinder_preterminal_coordinates_eq e hT
    (event_preterminal_surgery_free P F hpinch hT) s hs t ht hs' ht' x hx

end PoincareConjecture.M44
