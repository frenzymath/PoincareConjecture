import PoincareConjecture.Proofs.M47.CanonicalNeckBufferedBaseline
import PoincareConjecture.Proofs.M47.CanonicalNeckSlabTransport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47



theorem regularSlab_limit_not_buffered_neck
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {T c d b : ℝ}
    (N : SurgeryStrongNeck F T F.parameters.epsilon)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hU : (U : Set (F.slice T).carrier) = N.neck.carrier)
    (hd : d < -(N.neck.scale⁻¹ ^ 2)⁻¹) (hb : 0 < b)
    (E : SurgeryFlowCylinder F (F.slice T) T 1 (Icc d b) U)
    (hbased : ∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x)
    (hagree : ∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
      (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc d b), ∀ x ∈ U,
        HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x))
    (hTc : T < c) (hJ : Icc T c ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc T c))
    (times : ℕ → Icc T c) (points : ℕ → (F.slice T).carrier)
    (htimes : Tendsto (fun n => (times n).val) atTop (𝓝 T))
    (hpoints : Tendsto points atTop (𝓝 N.neck.center))
    (hbad : ∀ n, ¬ SurgeryCanonicalControl F (times n).val
      ((F.regular_slabs T c hTc hJ hfree).identify (times n) (points n))
      F.parameters.epsilon F.parameters.C) : False := by
  classical
  have hd0 : d < 0 := hd.trans (neg_neg_of_pos (inv_pos.mpr N.cylinder.scale_pos))
  have hzero : (0 : ℝ) ∈ Icc d b := ⟨hd0.le, hb.le⟩
  have hcenter : N.neck.center ∈ (U : Set (F.slice T).carrier) := by
    rw [hU]
    exact N.neck.central_sphere_subset N.neck.center_on_central_sphere
  let q : U := ⟨N.neck.center, hcenter⟩
  let t0 : Icc (T + d) (T + b) := ⟨T, by constructor <;> linarith only [hd0, hb]⟩
  have htimeMem : ∀ᶠ n in atTop, (times n).val ∈ Icc (T + d) (T + b) := by
    apply (htimes.eventually (Ioo_mem_nhds
      (show T + d < T by linarith only [hd0])
      (show T < T + b by linarith only [hb]))).mono
    exact fun _ hn => Ioo_subset_Icc_self hn
  have hpointMem : ∀ᶠ n in atTop, points n ∈ U :=
    hpoints.eventually (U.isOpen.mem_nhds hcenter)
  let tSeq : ℕ → Icc (T + d) (T + b) := fun n =>
    if h : (times n).val ∈ Icc (T + d) (T + b) then ⟨(times n).val, h⟩ else t0
  let xSeq : ℕ → U := fun n => if h : points n ∈ U then ⟨points n, h⟩ else q
  have htEq : (fun n => (tSeq n).val) =ᶠ[atTop] fun n => (times n).val := by
    filter_upwards [htimeMem] with n hn
    simp only [tSeq, dif_pos hn]
  have hxEq : (fun n => (xSeq n).val) =ᶠ[atTop] points := by
    filter_upwards [hpointMem] with n hn
    simp only [xSeq, dif_pos hn]
  have htSeq : Tendsto tSeq atTop (𝓝 t0) :=
    tendsto_subtype_rng.mpr (Tendsto.congr' htEq.symm htimes)
  have hxSeq : Tendsto xSeq atTop (𝓝 q) :=
    tendsto_subtype_rng.mpr (Tendsto.congr' hxEq.symm hpoints)
  have hnear := (htSeq.prodMk_nhds hxSeq).eventually
    (eventually_original_buffer_physical_necks P N U hU hd hb E hbased hagree q rfl)
  have hgood : ∀ᶠ n in atTop, SurgeryCanonicalControl F (times n).val
      ((F.regular_slabs T c hTc hJ hfree).identify (times n) (points n))
      F.parameters.epsilon F.parameters.C := by
    filter_upwards [hnear, htimeMem, hpointMem] with n hn htn hxn
    have htSeqEq : tSeq n = ⟨(times n).val, htn⟩ := dif_pos htn
    have hxSeqEq : xSeq n = ⟨points n, hxn⟩ := dif_pos hxn
    change ∃ S : SurgeryStrongNeck F (tSeq n).val F.parameters.epsilon,
      ∃ ht : (tSeq n).val - T ∈ Icc d b,
        HEq S.neck.center (E.forward ((tSeq n).val - T) ht (xSeq n).val) at hn
    rw [htSeqEq, hxSeqEq] at hn
    obtain ⟨S, ht, hline⟩ := hn
    have hphysical : T + ((times n).val - T) / 1 ∈ Icc T c := by
      simpa only [div_one, add_sub_cancel] using (times n).property
    have hslab := neck_buffer_regularSlab_forward E hzero hbased hTc hJ hfree
      ((times n).val - T) ht hphysical (points n) hxn
    have hidentify :
        HEq ((F.regular_slabs T c hTc hJ hfree).identify
          ⟨T + ((times n).val - T) / 1, hphysical⟩ (points n))
          ((F.regular_slabs T c hTc hJ hfree).identify (times n) (points n)) := by
      have transfer (s : ℝ) (hs : s ∈ Icc T c) (heq : s = (times n).val) :
          HEq ((F.regular_slabs T c hTc hJ hfree).identify ⟨s, hs⟩ (points n))
            ((F.regular_slabs T c hTc hJ hfree).identify (times n) (points n)) := by
        subst s
        rfl
      exact transfer _ hphysical (by simp only [div_one, add_sub_cancel])
    exact SurgeryCanonicalControl.neck S
      (eq_of_heq (hline.trans ((heq_of_eq hslab).trans hidentify)))
  obtain ⟨n, hn⟩ := hgood.exists
  exact hbad n hn

end PoincareConjecture.Proofs.M47
