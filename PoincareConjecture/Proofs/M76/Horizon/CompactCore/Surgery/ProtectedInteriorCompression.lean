import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.OriginalDiskCutCollars
import PoincareConjecture.Proofs.M76.Wall.ProtectedOpenRegion
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ProtectedRelativeFrontier

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem PLDomain.exists_protected_interior_compression_with_collars
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K C F : Set X} {j : V2 → X}
    (he : PLDomain e K) (hK : IsCompact K) (hR : IsClosed R) (hKR : K ⊆ R)
    (hC : IsClosed C) (hBC : frontier R ⊆ C) (hFR : F ⊆ R)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' F)
    (hfront : frontier K = frontier R ∪ F)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hjK : MapsTo j D K) (hjC : Disjoint (j '' D) C)
    (hproper : ∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q) :
    ∃ (P : OriginalDiskProduct e K j) (Fnew : Set X),
      MapsTo P.map (D ×ˢ I) (R \ C) ∧
      IsOpen ((Subtype.val : K → X) ⁻¹' P.openStrip) ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧ P.cutCarrier ⊆ K ∧
      Fnew = (F \ P.openStrip) ∪ P.endDisks ∧ IsCompact Fnew ∧
      Fnew ⊆ R \ C ∧ Disjoint (frontier R) Fnew ∧
      frontier P.cutCarrier = frontier R ∪ Fnew ∧
      frontier ((Subtype.val : R → X) ⁻¹' P.cutCarrier) =
        (Subtype.val : R → X) ⁻¹' Fnew ∧
      ((Subtype.val : R → X) ⁻¹' C ⊆
        interior ((Subtype.val : R → X) ⁻¹' P.cutCarrier)) ∧
      ((Subtype.val : R → X) ⁻¹' frontier R ⊆
        interior ((Subtype.val : R → X) ⁻¹' P.cutCarrier)) ∧
      Disjoint P.closedStrip C ∧ P.cutCarrier ∩ C = K ∩ C ∧
      interior P.cutCarrier = interior K \ P.closedStrip ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = K ∧ (interior P.cutCarrier).Nonempty ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : K → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier K → X) ⁻¹'
          (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨hU, hFU, _⟩ :=
    Set.protected_open_cut_region hC hBC hFR hprotect hrel hfront
  have hjU : j '' D ⊆ R \ C := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨hKR (hjK hz), fun h => disjoint_left.mp hjC ⟨z, hz, rfl⟩ h⟩
  have hjproper : ∀ z : D, j z ∈ frontier K ↔ (z : V2) ∈ Q := by
    intro z
    rw [hfront]
    constructor
    · rintro (hzB | hzF)
      · exact False.elim ((hjU ⟨z, z.property, rfl⟩).2 (hBC hzB))
      · exact (hproper z).mp hzF
    · exact fun hz => Or.inr ((hproper z).mpr hz)
  obtain ⟨P, hsmall, hopen, hPL, hcutK, hint, hcutfront, hoverlap, hcover, hne, hcollars⟩ :=
    exists_original_disk_cut_domain_with_collars hK he hj hemb hjK hjproper hU hjU
  let Fnew := (F \ P.openStrip) ∪ P.endDisks
  have hclosedStrip : IsClosed P.closedStrip :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
  have hstripU : P.closedStrip ⊆ R \ C := by
    rintro x ⟨z, hz, rfl⟩
    exact hsmall ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hopenclosed : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hendclosed : P.endDisks ⊆ P.closedStrip := fun _ hx => (hoverlap.symm ▸ hx).1
  have hstripC : Disjoint P.closedStrip C := disjoint_left.mpr (fun _ hx => (hstripU hx).2)
  have hnewU : Fnew ⊆ R \ C := by
    rintro x (hx | hx)
    · exact hFU hx.1
    · exact hstripU (hendclosed hx)
  have hnewB : Disjoint (frontier R) Fnew :=
    disjoint_left.mpr (fun _ hxB hx => (hnewU hx).2 (hBC hxB))
  have hnewfront : frontier P.cutCarrier = frontier R ∪ Fnew := by
    rw [hcutfront, hfront]
    ext x
    constructor
    · rintro (⟨hxB | hxF, hxnot⟩ | hxend)
      · exact Or.inl hxB
      · exact Or.inr (Or.inl ⟨hxF, hxnot⟩)
      · exact Or.inr (Or.inr hxend)
    · rintro (hxB | (hxF | hxend))
      · exact Or.inl ⟨Or.inl hxB, fun h =>
          disjoint_left.mp hstripC (hopenclosed h) (hBC hxB)⟩
      · exact Or.inl ⟨Or.inr hxF.1, hxF.2⟩
      · exact Or.inr hxend
  have hnewprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' P.cutCarrier) := by
    intro x hx
    let O := interior ((Subtype.val : R → X) ⁻¹' K) \
      (Subtype.val : R → X) ⁻¹' P.closedStrip
    have hO : IsOpen O := isOpen_interior.sdiff (hclosedStrip.preimage continuous_subtype_val)
    have hsub : O ⊆ (Subtype.val : R → X) ⁻¹' P.cutCarrier := by
      intro y hy
      exact ⟨(show y ∈ (Subtype.val : R → X) ⁻¹' K from interior_subset hy.1),
        fun h => hy.2 (hopenclosed h)⟩
    exact interior_maximal hsub hO ⟨hprotect hx, fun h => disjoint_left.mp hstripC h hx⟩
  have hnewprotectB : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → X) ⁻¹' P.cutCarrier) := fun _ hx => hnewprotect (hBC hx)
  have hcutR : P.cutCarrier ⊆ R := sdiff_subset.trans hKR
  have hnewint : Fnew ⊆ interior R := by
    intro x hx
    exact (mem_interior_iff_notMem_frontier (hnewU hx).1).mpr
      (fun h => (hnewU hx).2 (hBC h))
  have hnewrel := Set.protected_relative_frontier_eq_of_frontier hR hcutK.isClosed
    hcutR hnewint hnewprotectB hnewfront
  have hprecompact : IsCompact ((Subtype.val : R → X) ⁻¹' P.cutCarrier) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hcutK
      (fun x hx => ⟨⟨x, hcutR hx⟩, rfl⟩)
  have hprefront := hprecompact.of_isClosed_subset isClosed_frontier
    (hcutK.isClosed.preimage continuous_subtype_val).frontier_subset
  have hnewcompact : IsCompact Fnew := by
    have hh := hprefront.image continuous_subtype_val
    have himage : (Subtype.val : R → X) ''
        frontier ((Subtype.val : R → X) ⁻¹' P.cutCarrier) = Fnew := by
      rw [hnewrel]
      apply Subset.antisymm
      · rintro x ⟨y, hy, rfl⟩
        exact hy
      · intro x hx
        exact ⟨⟨x, (hnewU hx).1⟩, hx, rfl⟩
    exact himage ▸ hh
  have hfixed : P.cutCarrier ∩ C = K ∩ C := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun h => disjoint_left.mp hstripC (hopenclosed h) hx.2⟩, hx.2⟩
  exact ⟨P, Fnew, hsmall, hopen, hPL, hcutK, sdiff_subset, rfl, hnewcompact,
    hnewU, hnewB, hnewfront, hnewrel, hnewprotect, hnewprotectB, hstripC, hfixed,
    hint, hoverlap, hcover, hne, hcollars⟩

theorem PLDomain.exists_protected_interior_compression
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K C F : Set X} {j : V2 → X}
    (he : PLDomain e K) (hK : IsCompact K) (hR : IsClosed R) (hKR : K ⊆ R)
    (hC : IsClosed C) (hBC : frontier R ⊆ C) (hFR : F ⊆ R)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' F)
    (hfront : frontier K = frontier R ∪ F)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hjK : MapsTo j D K) (hjC : Disjoint (j '' D) C)
    (hproper : ∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q) :
    ∃ (P : OriginalDiskProduct e K j) (Fnew : Set X),
      MapsTo P.map (D ×ˢ I) (R \ C) ∧
      IsOpen ((Subtype.val : K → X) ⁻¹' P.openStrip) ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧ P.cutCarrier ⊆ K ∧
      Fnew = (F \ P.openStrip) ∪ P.endDisks ∧ IsCompact Fnew ∧
      Fnew ⊆ R \ C ∧ Disjoint (frontier R) Fnew ∧
      frontier P.cutCarrier = frontier R ∪ Fnew ∧
      frontier ((Subtype.val : R → X) ⁻¹' P.cutCarrier) =
        (Subtype.val : R → X) ⁻¹' Fnew ∧
      ((Subtype.val : R → X) ⁻¹' C ⊆
        interior ((Subtype.val : R → X) ⁻¹' P.cutCarrier)) ∧
      ((Subtype.val : R → X) ⁻¹' frontier R ⊆
        interior ((Subtype.val : R → X) ⁻¹' P.cutCarrier)) ∧
      Disjoint P.closedStrip C ∧ P.cutCarrier ∩ C = K ∩ C ∧
      interior P.cutCarrier = interior K \ P.closedStrip ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = K ∧ (interior P.cutCarrier).Nonempty := by
  obtain ⟨P, Fnew, hsmall, hopen, hPL, hcutK, hsub, heq, hcompact, hU, hB, hfront, hrel, hprotect, hprotectB, hC, hfixed, hint, hoverlap, hcover, hne, _⟩ :=
    PLDomain.exists_protected_interior_compression_with_collars he hK hR hKR hC hBC hFR hprotect hrel hfront hj hemb hjK hjC hproper
  exact ⟨P, Fnew, hsmall, hopen, hPL, hcutK, hsub, heq, hcompact, hU, hB, hfront, hrel, hprotect, hprotectB, hC, hfixed, hint, hoverlap, hcover, hne⟩

end PoincareConjecture.M76
