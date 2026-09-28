import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set Topology

namespace AddCircle

variable (p : ℝ) {Z : Type*} [TopologicalSpace Z]



def productSection : C(Z, Z × AddCircle p) :=
  ⟨fun z => (z, 0), continuous_id.prodMk continuous_const⟩



theorem range_productSection :
    range (productSection p (Z := Z)) = univ ×ˢ {(0 : AddCircle p)} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨mem_univ _, rfl⟩
  · intro hz
    exact ⟨z.1, Prod.ext rfl hz.2.symm⟩



theorem isEmbedding_productSection :
    IsEmbedding (productSection p (Z := Z)) :=
  isEmbedding_prodMkLeft 0



def productCutMap : C(Z × ℝ, Z × AddCircle p) :=
  ⟨fun z => (z.1, (z.2 : AddCircle p)),
    continuous_fst.prodMk ((AddCircle.continuous_mk' p).comp continuous_snd)⟩



theorem productCutMap_preimage_mark (A : Set Z) :
    productCutMap p ⁻¹' (A ×ˢ (univ : Set (AddCircle p))) = A ×ˢ univ := by
  ext z
  rfl



theorem productCutMap_endpoints (z : Z) :
    productCutMap p (z, 0) = productSection p z ∧
      productCutMap p (z, p) = productSection p z := by
  constructor
  · rfl
  · change (z, ((p : ℝ) : AddCircle p)) = (z, 0)
    rw [coe_period]

variable [Fact (0 < p)]



theorem productCutMap_image :
    productCutMap p '' ((univ : Set Z) ×ˢ Icc 0 p) = univ := by
  ext z
  constructor
  · intro _
    exact mem_univ _
  · intro _
    obtain ⟨t, ht, he⟩ := eq_coe_Ico z.2
    exact ⟨(z.1, t), ⟨mem_univ _, ht.1, ht.2.le⟩, Prod.ext rfl he⟩



theorem productCutMap_mem_section {z : Z × ℝ} (hz : z.2 ∈ Icc 0 p) :
    productCutMap p z ∈ range (productSection p) ↔ z.2 = 0 ∨ z.2 = p := by
  rw [range_productSection]
  change (True ∧ (z.2 : AddCircle p) = 0) ↔ _
  rw [true_and]
  exact coe_eq_zero_iff_endpoints hz



theorem productCutMap_eq_iff {z w : Z × ℝ}
    (hz : z.2 ∈ Icc 0 p) (hw : w.2 ∈ Icc 0 p) :
    productCutMap p z = productCutMap p w ↔
      z.1 = w.1 ∧ (z.2 = w.2 ∨ (z.2 = 0 ∧ w.2 = p) ∨
        (z.2 = p ∧ w.2 = 0)) := by
  change (z.1, (z.2 : AddCircle p)) = (w.1, (w.2 : AddCircle p)) ↔ _
  rw [Prod.mk.injEq, coe_eq_coe_iff_eq_or_endpoints hz hw]




theorem isQuotientMap_productCut [CompactSpace Z] [T2Space Z] :
    IsQuotientMap (fun z : Z × Icc (0 : ℝ) p =>
      (z.1, ((z.2 : ℝ) : AddCircle p))) := by
  let q : Z × Icc (0 : ℝ) p → Z × AddCircle p :=
    fun z => (z.1, ((z.2 : ℝ) : AddCircle p))
  have hc : Continuous q := continuous_fst.prodMk
    ((AddCircle.continuous_mk' p).comp (continuous_subtype_val.comp continuous_snd))
  have hs : Function.Surjective q := by
    intro z
    obtain ⟨t, ht, he⟩ := eq_coe_Ico z.2
    exact ⟨(z.1, ⟨t, ht.1, ht.2.le⟩), Prod.ext rfl he⟩
  exact hc.isClosedMap.isQuotientMap hc hs

end AddCircle
