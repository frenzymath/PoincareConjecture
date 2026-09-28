import PoincareConjecture.Proofs.M47.SeedM15Cylinder
import PoincareConjecture.Proofs.M47.SeedCylinderClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

private theorem forward_heq_of_time_eq
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin Q I U) {s t : ℝ}
    (hs : s ∈ I) (ht : t ∈ I) (hst : s = t) (x : C.carrier) :
    HEq (e.forward s hs x) (e.forward t ht x) := by
  cases hst
  rfl

theorem terminalCommonInterval_physical_eq
    {F : SurgeryFlowData.{u}} {C D : GeneralizedSliceCarrier.{u}}
    {origin Q a : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}
    (e : SurgeryFlowCylinder F C origin Q I U)
    (f : SurgeryFlowCylinder F D origin Q J V)
    (ha : a ≤ 0) (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J)
    (x : C.carrier) (hx : x ∈ U) (y : D.carrier) (hy : y ∈ V)
    (hterminal : e.forward 0 (hI ⟨ha, le_rfl⟩) x =
      f.forward 0 (hJ ⟨ha, le_rfl⟩) y) :
    e.forward a (hI ⟨le_rfl, ha⟩) x = f.forward a (hJ ⟨le_rfl, ha⟩) y := by
  have hQ := e.scale_pos
  have hmem : MapsTo (fun z : ℝ => Q * z) (Icc (a / Q) 0) (Icc a 0) := by
    intro z hz
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hQ).mp hz.1,
      mul_nonpos_of_nonneg_of_nonpos hQ.le hz.2⟩
  have hmono : StrictMonoOn (fun z : ℝ => Q * z) (Icc (a / Q) 0) :=
    fun _ _ _ _ h => mul_lt_mul_of_pos_left h hQ
  have hclock (z : ℝ) (_hz : z ∈ Icc (a / Q) 0) :
      origin + z / 1 = origin + (Q * z) / Q := by
    rw [div_one, mul_div_cancel_left₀ z hQ.ne']
  let e' := Proofs.M47.seedCylinderReclock e (by norm_num : (0 : ℝ) < 1)
    ordConnected_Icc (fun z => Q * z) (fun _ hz => hI (hmem hz)) hmono hclock
  let f' := Proofs.M47.seedCylinderReclock f (by norm_num : (0 : ℝ) < 1)
    ordConnected_Icc (fun z => Q * z) (fun _ hz => hJ (hmem hz)) hmono hclock
  have heread (z : ℝ) (hz : z ∈ Icc (a / Q) 0) :
      HEq (e'.forward z hz x) (e.forward (Q * z) (hI (hmem hz)) x) :=
    Proofs.M47.seedCylinderReclock_forward_heq e (by norm_num) ordConnected_Icc
      (fun z => Q * z) (fun _ hz => hI (hmem hz)) hmono hclock z hz x
  have hfread (z : ℝ) (hz : z ∈ Icc (a / Q) 0) :
      HEq (f'.forward z hz y) (f.forward (Q * z) (hJ (hmem hz)) y) :=
    Proofs.M47.seedCylinderReclock_forward_heq f (by norm_num) ordConnected_Icc
      (fun z => Q * z) (fun _ hz => hJ (hmem hz)) hmono hclock z hz y
  have haQ : a / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha hQ.le
  have hzero : (0 : ℝ) ∈ Icc (a / Q) 0 := ⟨haQ, le_rfl⟩
  have he0 : HEq (e'.forward 0 hzero x) (e.forward 0 (hI ⟨ha, le_rfl⟩) x) := by
    exact (heread 0 hzero).trans (forward_heq_of_time_eq e _ _ (mul_zero Q) x)
  have hf0 : HEq (f'.forward 0 hzero y) (f.forward 0 (hJ ⟨ha, le_rfl⟩) y) := by
    exact (hfread 0 hzero).trans (forward_heq_of_time_eq f _ _ (mul_zero Q) y)
  have hagree := seedM15_cylinder_eq_of_terminal e' f' haQ (Subset.refl _)
    (Subset.refl _) x hx y hy (eq_of_heq (he0.trans ((heq_of_eq hterminal).trans hf0.symm)))
  have hparam : Q * (a / Q) = a := by field_simp
  have hea : HEq (e'.forward (a / Q) ⟨le_rfl, haQ⟩ x)
      (e.forward a (hI ⟨le_rfl, ha⟩) x) := by
    exact (heread (a / Q) ⟨le_rfl, haQ⟩).trans (forward_heq_of_time_eq e _ _ hparam x)
  have hfa : HEq (f'.forward (a / Q) ⟨le_rfl, haQ⟩ y)
      (f.forward a (hJ ⟨le_rfl, ha⟩) y) := by
    exact (hfread (a / Q) ⟨le_rfl, haQ⟩).trans (forward_heq_of_time_eq f _ _ hparam y)
  exact eq_of_heq (hea.symm.trans ((heq_of_eq hagree).trans hfa))

theorem terminalCommonInterval_generalized_eq
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {C D : GeneralizedSliceCarrier.{u}}
    {origin Q a : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}
    (e : GeneralizedFlowCylinder H.generalized C origin Q I U)
    (f : GeneralizedFlowCylinder H.generalized D origin Q J V)
    (hIc : I.OrdConnected) (hJc : J.OrdConnected) (hU : IsOpen U) (hV : IsOpen V)
    (ha : a ≤ 0) (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J)
    (x : C.carrier) (hx : x ∈ U) (y : D.carrier) (hy : y ∈ V)
    (hterminal : e.pointMap 0 (hI ⟨ha, le_rfl⟩) x =
      f.pointMap 0 (hJ ⟨ha, le_rfl⟩) y) :
    e.forward a (hI ⟨le_rfl, ha⟩) x = f.forward a (hJ ⟨le_rfl, ha⟩) y := by
  have heTime (s : ℝ) (hs : s ∈ I) : origin + s / Q ∈ H.generalized.interval :=
    (H.generalized.slice_nonempty_iff _).mp ⟨e.forward s hs x⟩
  have hfTime (s : ℝ) (hs : s ∈ J) : origin + s / Q ∈ H.generalized.interval :=
    (H.generalized.slice_nonempty_iff _).mp ⟨f.forward s hs y⟩
  obtain ⟨ep, hep, _hepmetric⟩ := H.cylinders_to_surgery C origin Q I U hIc hU heTime e
  obtain ⟨fp, hfp, _hfpmetric⟩ := H.cylinders_to_surgery D origin Q J V hJc hV hfTime f
  have hzero : e.forward 0 (hI ⟨ha, le_rfl⟩) x = f.forward 0 (hJ ⟨ha, le_rfl⟩) y :=
    eq_of_heq (Sigma.mk.inj hterminal).2
  have hphysical : ep.forward 0 (hI ⟨ha, le_rfl⟩) x =
      fp.forward 0 (hJ ⟨ha, le_rfl⟩) y := by
    rw [hep _ _ x hx, hfp _ _ y hy, hzero]
  have hagree := terminalCommonInterval_physical_eq ep fp ha hI hJ x hx y hy hphysical
  rw [hep _ _ x hx, hfp _ _ y hy] at hagree
  exact (H.history.forward_openEmbedding _ _).injective hagree

theorem terminalCommonInterval_pullback_eq
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {C : GeneralizedSliceCarrier.{u}}
    {origin Q a : ℝ} {I J : Set ℝ} {U V : Set C.carrier}
    (e : GeneralizedFlowCylinder H.generalized C origin Q I U)
    (f : GeneralizedFlowCylinder H.generalized C origin Q J V)
    (hIc : I.OrdConnected) (hJc : J.OrdConnected) (hU : IsOpen U) (hV : IsOpen V)
    (ha : a ≤ 0) (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J)
    (hterminal : ∀ x ∈ U ∩ V, e.pointMap 0 (hI ⟨ha, le_rfl⟩) x =
      f.pointMap 0 (hJ ⟨ha, le_rfl⟩) x)
    {x : C.carrier} (hx : x ∈ U ∩ V) (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner a (hI ⟨le_rfl, ha⟩) x v w =
      f.pullbackInner a (hJ ⟨le_rfl, ha⟩) x v w := by
  have heq : e.forward a (hI ⟨le_rfl, ha⟩) =ᶠ[𝓝 x] f.forward a (hJ ⟨le_rfl, ha⟩) := by
    filter_upwards [(hU.inter hV).mem_nhds hx] with y hy
    exact terminalCommonInterval_generalized_eq H e f hIc hJc hU hV ha hI hJ
      y hy.1 y hy.2 (hterminal y hy)
  unfold GeneralizedFlowCylinder.pullbackInner
  rw [heq.self_of_nhds, heq.mfderiv_eq]

end PoincareConjecture.M47
