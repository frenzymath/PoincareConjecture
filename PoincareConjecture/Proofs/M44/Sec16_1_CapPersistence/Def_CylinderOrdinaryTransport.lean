import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_OpenRegularCylinder

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

theorem cylinder_regularIdentifyIco
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale b : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (r : ℝ) (hr : r ∈ I)
    (hJ : Ico (origin + r / scale) b ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioo (origin + r / scale) b))
    (s : ℝ) (hs : s ∈ I) (hs' : origin + s / scale ∈ Ico (origin + r / scale) b)
    (x : C.carrier) (hx : x ∈ U) :
    F.regularIdentifyIco hJ hNo ⟨origin + s / scale, hs'⟩ (e.forward r hr x) =
      e.forward s hs x := by
  let z := (origin + s / scale + b) / 2
  have haz : origin + r / scale < z := by dsimp [z]; linarith [hs'.1, hs'.2]
  have hsz : origin + s / scale ≤ z := by dsimp [z]; linarith [hs'.2]
  have hzb : z < b := by dsimp [z]; linarith [hs'.2]
  have hK : Icc (origin + r / scale) z ⊆ F.time_domain :=
    fun _ ht => hJ ⟨ht.1, ht.2.trans_lt hzb⟩
  have hfree : Disjoint F.surgery_times (Ioc (origin + r / scale) z) :=
    Set.disjoint_left.mpr fun _ ht hu => Set.disjoint_left.mp hNo ht ⟨hu.1, hu.2.trans_lt hzb⟩
  rw [F.regularIdentifyIco_eq hJ hNo ⟨origin + s / scale, hs'⟩ haz hK hfree ⟨hs'.1, hsz⟩]
  have h := e.slab_compatibility (origin + r / scale) z haz hK hfree
    r hr s hs ⟨le_rfl, haz.le⟩ ⟨hs'.1, hsz⟩ x hx
  simpa only [SurgeryRegularSlab.transport_initial] using h

end PoincareConjecture.M44
