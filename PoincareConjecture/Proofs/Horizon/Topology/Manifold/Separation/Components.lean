import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Sign
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Connected

open Set Topology

namespace Poincare.Topology

theorem exists_collar_complementary_regions
    {Y X : Type*} [TopologicalSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    [TopologicalSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {r : ℝ} (hr : 0 < r) {U : Set X}
    (hU : IsOpen U) (e : (Y × Ioo (-r) r) ≃ₜ U) :
    let S := range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X))
    ∃ A B : Set X,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Sᶜ ∧ frontier A = S ∧ frontier B = S ∧
      (fun z => (e z : X)) '' {z | (z.2 : ℝ) < 0} ⊆ A ∧
      (fun z => (e z : X)) '' {z | 0 < (z.2 : ℝ)} ⊆ B := by
  dsimp only
  let S := range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X))
  obtain ⟨f, hf, hzero⟩ := exists_collarSign r hr hU e
  let A : Set X := f ⁻¹' Iio 0
  let B : Set X := f ⁻¹' Ioi 0
  have hA : IsOpen A := isOpen_Iio.preimage f.continuous
  have hB : IsOpen B := isOpen_Ioi.preimage f.continuous
  have hneg (z : Y × Ioo (-r) r) : (e z : X) ∈ A ↔ (z.2 : ℝ) < 0 := by
    change f (e z : X) < 0 ↔ _
    rw [hf z.1 z.2, collarClamp_neg_iff hr]
  have hpos (z : Y × Ioo (-r) r) : (e z : X) ∈ B ↔ 0 < (z.2 : ℝ) := by
    change 0 < f (e z : X) ↔ _
    rw [hf z.1 z.2, collarClamp_pos_iff hr]
  have hL : (fun z => (e z : X)) '' {z | (z.2 : ℝ) < 0} ⊆ A := by
    rintro x ⟨z, hz, rfl⟩
    exact (hneg z).mpr hz
  have hR : (fun z => (e z : X)) '' {z | 0 < (z.2 : ℝ)} ⊆ B := by
    rintro x ⟨z, hz, rfl⟩
    exact (hpos z).mpr hz
  have hAU : A ∩ U = (fun z => (e z : X)) '' {z | (z.2 : ℝ) < 0} := by
    ext x
    constructor
    · rintro ⟨hxA, hxU⟩
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hxU⟩
      have hzx := congrArg Subtype.val hz
      exact ⟨z, (hneg z).mp (hzx.symm ▸ hxA), hzx⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hneg z).mpr hz, (e z).property⟩
  have hBU : B ∩ U = (fun z => (e z : X)) '' {z | 0 < (z.2 : ℝ)} := by
    ext x
    constructor
    · rintro ⟨hxB, hxU⟩
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hxU⟩
      have hzx := congrArg Subtype.val hz
      exact ⟨z, (hpos z).mp (hzx.symm ▸ hxB), hzx⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hpos z).mpr hz, (e z).property⟩
  have hdis : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact lt_asymm (show f x < 0 from hx) (show 0 < f x from hy)
  have hSA : frontier A ⊆ S := by
    intro x hx
    apply (hzero x).mp
    have h := f.continuous.frontier_preimage_subset (Iio 0) hx
    simpa only [frontier_Iio, mem_preimage, mem_singleton_iff] using h
  have hSB : frontier B ⊆ S := by
    intro x hx
    apply (hzero x).mp
    have h := f.continuous.frontier_preimage_subset (Ioi 0) hx
    simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using h
  have hSU : S ⊆ U := by
    rintro x ⟨y, rfl⟩
    exact (e _).property
  have hAc : IsConnected (A ∩ U) := hAU ▸ isConnected_collar_negative hr e
  have hBc : IsConnected (B ∩ U) := hBU ▸ isConnected_collar_positive hr e
  have hAne : A ≠ univ := by
    intro h
    obtain ⟨x, hxB, _⟩ := hBc.nonempty
    exact Set.disjoint_left.mp hdis (h ▸ mem_univ x) hxB
  have hBne : B ≠ univ := by
    intro h
    obtain ⟨x, hxA, _⟩ := hAc.nonempty
    exact Set.disjoint_left.mp hdis hxA (h ▸ mem_univ x)
  refine ⟨A, B, hA, hB,
    isConnected_of_inter_of_frontier_subset hA hU hAc (hSA.trans hSU) hAne,
    isConnected_of_inter_of_frontier_subset hB hU hBc (hSB.trans hSU) hBne,
    hdis, ?_, Subset.antisymm hSA ?_, Subset.antisymm hSB ?_, hL, hR⟩
  · ext x
    change (f x < 0 ∨ 0 < f x) ↔ x ∉ S
    rw [← hzero x]
    exact lt_or_lt_iff_ne
  · rintro x ⟨y, rfl⟩
    refine ⟨closure_mono hL (collar_center_mem_closure_negative hr e y), ?_⟩
    intro hi
    have h := interior_subset hi
    change f (e (y, ⟨0, _⟩) : X) < 0 at h
    rw [hf, collarClamp_zero] at h
    exact lt_irrefl _ h
  · rintro x ⟨y, rfl⟩
    refine ⟨closure_mono hR (collar_center_mem_closure_positive hr e y), ?_⟩
    intro hi
    have h := interior_subset hi
    change 0 < f (e (y, ⟨0, _⟩) : X) at h
    rw [hf, collarClamp_zero] at h
    exact lt_irrefl _ h

end Poincare.Topology
