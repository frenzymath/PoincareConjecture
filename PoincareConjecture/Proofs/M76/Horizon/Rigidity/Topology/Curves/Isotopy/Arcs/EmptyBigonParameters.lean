import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.EmptyBigon



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : P2 → ℝ) ⁻¹' ({0} : Set ℝ))

theorem empty_returning_bigon_parameter_data
    {q : ℝ → P2} (hi : InjOn q (Icc 0 1))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    {u v : P2} {B C : Set P2}
    (hpairs : ({u, v} : Set P2) = {q a, q b})
    (hW : q '' Icc a b ⊆ B) (hup : ∀ x ∈ B, 0 ≤ x.2)
    (hBaxis : B ∩ Z = segment ℝ u v)
    (hC : q '' Icc (0 : ℝ) 1 ⊆ C) (hbase : C ∩ segment ℝ u v = {u, v}) :
    (q a).2 = 0 ∧ (q b).2 = 0 ∧ ∀ s ∈ Ioo a b, 0 < (q s).2 := by
  have hends (x : P2) (hx : x ∈ ({u, v} : Set P2)) : x.2 = 0 := by
    have hxseg : x ∈ segment ℝ u v := by
      rcases hx with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    exact (hBaxis.symm.subset hxseg).2
  have hqa := hends (q a) (hpairs.symm.subset (by simp))
  have hqb := hends (q b) (hpairs.symm.subset (by simp))
  refine ⟨hqa, hqb, ?_⟩
  intro s hs
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs.1.le, hs.2.le.trans hb⟩
  have hsB : q s ∈ B := hW (mem_image_of_mem q (Ioo_subset_Icc_self hs))
  apply lt_of_le_of_ne (hup _ hsB)
  intro he
  have hsseg := hBaxis.subset ⟨hsB, he.symm⟩
  have hsends := hpairs.subset (hbase.subset ⟨hC (mem_image_of_mem q hsI), hsseg⟩)
  rcases hsends with hsqa | hsqb
  · have := hi hsI ⟨ha, hab.le.trans hb⟩ hsqa
    linarith [hs.1]
  · have := hi hsI ⟨ha.trans hab.le, hb⟩ hsqb
    linarith [hs.2]

theorem finitePL_annularLiftAboveAxis {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (c : ℝ) :
    FinitePiecewiseAffineOn (annularLiftAboveAxis r c) (Icc 0 1) :=
  hr.postcomp ((ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap.prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap - ContinuousAffineMap.const ℝ P2 c))

theorem injOn_annularLiftAboveAxis {r : ℝ → P2}
    (hi : InjOn r (Icc 0 1)) (c : ℝ) :
    InjOn (annularLiftAboveAxis r c) (Icc 0 1) := by
  intro s hs t ht he
  apply hi hs ht
  have hfst := congrArg Prod.fst he
  have hsnd := congrArg Prod.snd he
  apply Prod.ext
  · change (r s).1 - c = (r t).1 - c at hsnd
    linarith
  · exact hfst

end PoincareConjecture.M76.Dehn
