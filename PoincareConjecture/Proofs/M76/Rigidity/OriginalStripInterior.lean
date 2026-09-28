import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import Mathlib.Topology.Order.DenselyOrdered









set_option autoImplicit false

open Set Metric Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}



theorem OriginalDiskProduct.strip_core_eq (P : OriginalDiskProduct e R j)
    {δ : ℝ} (hδ : δ ≤ 1) :
    P.map '' (ball (0 : V2) 1 ×ˢ Ioo (-δ) δ) =
      (P.map '' (D ×ˢ Ioo (-δ) δ)) ∩ interior R := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzD : z.1 ∈ D \ Q := by
      simpa only [closedBall_sdiff_sphere] using hz.1
    have ht : z.2 ∈ I := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    refine ⟨⟨z, ⟨hzD.1, hz.2⟩, rfl⟩,
      (mem_interior_iff_notMem_frontier (P.inside ⟨hzD.1, ht⟩)).mpr ?_⟩
    exact fun h => hzD.2 ((P.proper z ⟨hzD.1, ht⟩).mp h)
  · rintro ⟨⟨z, hz, rfl⟩, hy⟩
    have ht : z.2 ∈ I := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    refine ⟨z, ⟨?_, hz.2⟩, rfl⟩
    rw [← closedBall_sdiff_sphere]
    refine ⟨hz.1, ?_⟩
    intro hq
    exact ((P.proper z ⟨hz.1, ht⟩).mpr hq).2 hy



theorem OriginalDiskProduct.isOpen_strip_core (P : OriginalDiskProduct e R j)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D ×ˢ Ioo (-δ) δ)))) :
    IsOpen (P.map '' (ball (0 : V2) 1 ×ˢ Ioo (-δ) δ)) := by
  obtain ⟨O, hO, hval⟩ := hopen.image_val
  have hstrip : P.map '' (D ×ˢ Ioo (-δ) δ) = O ∩ R := by
    rw [← hval]
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hy
      have ht : z.2 ∈ I := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
      exact ⟨⟨P.map z, P.inside ⟨hz.1, ht⟩⟩, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  rw [P.strip_core_eq hδ, hstrip, inter_assoc,
    inter_eq_self_of_subset_right interior_subset]
  exact hO.inter isOpen_interior




theorem OriginalDiskProduct.interior_closed_strip (P : OriginalDiskProduct e R j)
    {δ : ℝ} (hδ : δ < 1)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D ×ˢ Ioo (-δ) δ)))) :
    interior (P.map '' (D ×ˢ Icc (-δ) δ)) =
      P.map '' (ball (0 : V2) 1 ×ˢ Ioo (-δ) δ) := by
  let C := P.map '' (D ×ˢ Icc (-δ) δ)
  have hfull : D ×ˢ Icc (-δ) δ ⊆ D ×ˢ I := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hCR : C ⊆ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact P.inside (hfull hz)
  apply Subset.antisymm
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := interior_subset hx
    have htI : I ∈ 𝓝 z.2 := Icc_mem_nhds
      (by linarith [hz.2.1]) (by linarith [hz.2.2])
    have hc : ContinuousOn (fun t : ℝ => P.map (z.1, t)) I :=
      P.polyhedral.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hz.1, ht⟩)
    have hcAt : ContinuousAt (fun t : ℝ => P.map (z.1, t)) z.2 :=
      (hc z.2 (hfull hz).2).continuousAt htI
    have hn : (fun t : ℝ => P.map (z.1, t)) ⁻¹' interior C ∈ 𝓝 z.2 :=
      hcAt.preimage_mem_nhds (isOpen_interior.mem_nhds hx)
    have hsmall : Icc (-δ) δ ∈ 𝓝 z.2 := by
      apply Filter.mem_of_superset (inter_mem hn htI)
      intro t ht
      obtain ⟨w, hw, hwz⟩ := interior_subset ht.1
      have heq : w = (z.1, t) := P.injective (hfull hw)
        (show (z.1, t) ∈ D ×ˢ I from ⟨hz.1, ht.2⟩) hwz
      have hwtime : w.2 = t := congrArg Prod.snd heq
      rw [← hwtime]
      exact hw.2
    have ht : z.2 ∈ Ioo (-δ) δ := by
      have h := mem_interior_iff_mem_nhds.mpr hsmall
      simpa only [interior_Icc] using h
    rw [P.strip_core_eq hδ.le]
    exact ⟨⟨z, ⟨hz.1, ht⟩, rfl⟩, interior_mono hCR hx⟩
  · apply (P.isOpen_strip_core hδ.le hopen).subset_interior_iff.mpr
    exact image_mono (prod_mono ball_subset_closedBall Ioo_subset_Icc_self)

end PoincareConjecture.M76
