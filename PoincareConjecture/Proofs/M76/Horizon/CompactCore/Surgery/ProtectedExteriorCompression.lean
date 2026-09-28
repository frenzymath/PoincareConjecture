import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ExteriorDiskAttachment
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
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem PLDomain.exists_protected_exterior_compression_with_collars
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
    (hjext : MapsTo j D (interior K)ᶜ) (hjR : MapsTo j D R)
    (hjC : Disjoint (j '' D) C)
    (hproper : ∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q) :
    ∃ H L : Set X,
      IsCompact H ∧ PLDomain e H ∧ K ∪ j '' D ⊆ interior H ∧
      L = H ∩ (interior K)ᶜ ∧ IsCompact L ∧ PLDomain e L ∧
      ∃ (P : OriginalDiskProduct e L j) (Fnew : Set X),
        MapsTo P.map (D ×ˢ I) (interior H ∩ (R \ C)) ∧
        IsOpen ((Subtype.val : L → X) ⁻¹' P.openStrip) ∧
        PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
        PLDomain e (K ∪ P.closedStrip) ∧ IsCompact (K ∪ P.closedStrip) ∧
        K ∪ P.closedStrip ⊆ R ∧
        P.closedStrip ∩ K = P.map '' (Q ×ˢ J) ∧
        Fnew = (F \ P.openStrip) ∪ P.endDisks ∧ IsCompact Fnew ∧
        Fnew ⊆ R \ C ∧ Disjoint (frontier R) Fnew ∧
        frontier (K ∪ P.closedStrip) = frontier R ∪ Fnew ∧
        frontier ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip)) =
          (Subtype.val : R → X) ⁻¹' Fnew ∧
        ((Subtype.val : R → X) ⁻¹' C ⊆
          interior ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip))) ∧
        ((Subtype.val : R → X) ⁻¹' frontier R ⊆
          interior ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip))) ∧
        Disjoint P.closedStrip C ∧ (K ∪ P.closedStrip) ∩ C = K ∩ C ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          IsOpen ((Subtype.val : L → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
          IsOpen ((Subtype.val : frontier L → X) ⁻¹'
            (P.map '' (Q ×ˢ Ioo (-ε) ε))) ∧
          IsOpen ((Subtype.val : frontier K → X) ⁻¹'
            (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨hU, hFU, _⟩ :=
    Set.protected_open_cut_region hC hBC hFR hprotect hrel hfront
  have hjU : j '' D ⊆ R \ C := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨hjR hz, fun h => disjoint_left.mp hjC ⟨z, hz, rfl⟩ h⟩
  have hjproper : ∀ z : D, j z ∈ frontier K ↔ (z : V2) ∈ Q := by
    intro z
    rw [hfront]
    constructor
    · rintro (hzB | hzF)
      · exact False.elim ((hjU ⟨z, z.property, rfl⟩).2 (hBC hzB))
      · exact (hproper z).mp hzF
    · exact fun hz => Or.inr ((hproper z).mpr hz)
  obtain ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, hLfront,
    P, hsmall, hopen, hcutPL, hcutcompact, hint, hcutfront, hoverlap, hcover, hne, hcollars⟩ :=
    he.exists_compact_exterior_disk_cut_with_collars hK hj hemb hjext hjproper hU hjU
  have hstrip : P.closedStrip ⊆ interior H ∩ (R \ C) := by
    rintro x ⟨z, hz, rfl⟩
    exact hsmall ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨hnewPL, hnewcompact, _, _, hnewfront0, hnewcollars⟩ :=
    P.exterior_attachment_geometry_with_collars he hK (fun _ hx => hcore (Or.inl hx)) hLE hLfront
      (fun _ hx => (hstrip hx).1) hcutPL hint hcutfront hoverlap hcollars
  have hnewR : K ∪ P.closedStrip ⊆ R := union_subset hKR (fun _ hx => (hstrip hx).2.1)
  have hstripC : Disjoint P.closedStrip C :=
    disjoint_left.mpr (fun _ hx => (hstrip hx).2.2)
  have hopenclosed : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hendclosed : P.endDisks ⊆ P.closedStrip := fun _ hx => (hoverlap.symm ▸ hx).1
  have hfoot : P.closedStrip ∩ K = P.map '' (Q ×ˢ J) := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxK⟩
      have hzfull : z ∈ D ×ˢ I := ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      have hxext : P.map z ∉ interior K := (hLE.subset (P.inside hzfull)).2
      have hxfront : P.map z ∈ frontier L :=
        hLfront.symm.subset (Or.inl ⟨subset_closure hxK, hxext⟩)
      exact ⟨z, ⟨(P.proper z hzfull).mp hxfront, hz.2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hzfull : z ∈ D ×ˢ I :=
        ⟨sphere_subset_closedBall hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      refine ⟨⟨z, ⟨sphere_subset_closedBall hz.1, hz.2⟩, rfl⟩, ?_⟩
      rcases hLfront.subset ((P.proper z hzfull).mpr hz.1) with hxK | hxH
      · exact he.closed.frontier_subset hxK
      · exact False.elim (hxH.1.2 (hsmall hzfull).1)
  let Fnew := (F \ P.openStrip) ∪ P.endDisks
  have hnewU : Fnew ⊆ R \ C := by
    rintro x (hx | hx)
    · exact hFU hx.1
    · exact (hstrip (hendclosed hx)).2
  have hnewB : Disjoint (frontier R) Fnew :=
    disjoint_left.mpr (fun _ hxB hx => (hnewU hx).2 (hBC hxB))
  have hnewfront : frontier (K ∪ P.closedStrip) = frontier R ∪ Fnew := by
    rw [hnewfront0, hfront]
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
      interior ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip)) :=
    hprotect.trans (interior_mono (preimage_mono subset_union_left))
  have hnewprotectB : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip)) :=
    fun _ hx => hnewprotect (hBC hx)
  have hnewint : Fnew ⊆ interior R := by
    intro x hx
    exact (mem_interior_iff_notMem_frontier (hnewU hx).1).mpr
      (fun h => (hnewU hx).2 (hBC h))
  have hnewrel := Set.protected_relative_frontier_eq_of_frontier hR hnewcompact.isClosed
    hnewR hnewint hnewprotectB hnewfront
  have hprecompact : IsCompact ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hnewcompact
      (fun x hx => ⟨⟨x, hnewR hx⟩, rfl⟩)
  have hprefront := hprecompact.of_isClosed_subset isClosed_frontier
    (hnewcompact.isClosed.preimage continuous_subtype_val).frontier_subset
  have hFcompact : IsCompact Fnew := by
    have hh := hprefront.image continuous_subtype_val
    have himage : (Subtype.val : R → X) ''
        frontier ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip)) = Fnew := by
      rw [hnewrel]
      apply Subset.antisymm
      · rintro x ⟨y, hy, rfl⟩
        exact hy
      · intro x hx
        exact ⟨⟨x, (hnewU hx).1⟩, hx, rfl⟩
    exact himage ▸ hh
  have hfixed : (K ∪ P.closedStrip) ∩ C = K ∩ C := by
    ext x
    constructor
    · rintro ⟨hxK | hxstrip, hxC⟩
      · exact ⟨hxK, hxC⟩
      · exact False.elim (disjoint_left.mp hstripC hxstrip hxC)
    · exact fun hx => ⟨Or.inl hx.1, hx.2⟩
  exact ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, P, Fnew,
    hsmall, hopen, hcutPL, hcutcompact, hnewPL, hnewcompact, hnewR, hfoot,
    rfl, hFcompact, hnewU, hnewB, hnewfront, hnewrel, hnewprotect, hnewprotectB,
    hstripC, hfixed, hnewcollars⟩

theorem PLDomain.exists_protected_exterior_compression
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
    (hjext : MapsTo j D (interior K)ᶜ) (hjR : MapsTo j D R)
    (hjC : Disjoint (j '' D) C)
    (hproper : ∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q) :
    ∃ H L : Set X,
      IsCompact H ∧ PLDomain e H ∧ K ∪ j '' D ⊆ interior H ∧
      L = H ∩ (interior K)ᶜ ∧ IsCompact L ∧ PLDomain e L ∧
      ∃ (P : OriginalDiskProduct e L j) (Fnew : Set X),
        MapsTo P.map (D ×ˢ I) (interior H ∩ (R \ C)) ∧
        IsOpen ((Subtype.val : L → X) ⁻¹' P.openStrip) ∧
        PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
        PLDomain e (K ∪ P.closedStrip) ∧ IsCompact (K ∪ P.closedStrip) ∧
        K ∪ P.closedStrip ⊆ R ∧
        P.closedStrip ∩ K = P.map '' (Q ×ˢ J) ∧
        Fnew = (F \ P.openStrip) ∪ P.endDisks ∧ IsCompact Fnew ∧
        Fnew ⊆ R \ C ∧ Disjoint (frontier R) Fnew ∧
        frontier (K ∪ P.closedStrip) = frontier R ∪ Fnew ∧
        frontier ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip)) =
          (Subtype.val : R → X) ⁻¹' Fnew ∧
        ((Subtype.val : R → X) ⁻¹' C ⊆
          interior ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip))) ∧
        ((Subtype.val : R → X) ⁻¹' frontier R ⊆
          interior ((Subtype.val : R → X) ⁻¹' (K ∪ P.closedStrip))) ∧
        Disjoint P.closedStrip C ∧ (K ∪ P.closedStrip) ∩ C = K ∩ C := by
  obtain ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, P, Fnew, hsmall, hopen, hcutPL, hcutcompact, hnewPL, hnewcompact, hnewR, hfoot, heq, hFcompact, hnewU, hnewB, hnewfront, hnewrel, hnewprotect, hnewprotectB, hstripC, hfixed, _⟩ :=
    PLDomain.exists_protected_exterior_compression_with_collars
      he hK hR hKR hC hBC hFR hprotect hrel hfront hj hemb hjext hjR hjC hproper
  exact ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, P, Fnew, hsmall, hopen, hcutPL, hcutcompact, hnewPL, hnewcompact, hnewR, hfoot, heq, hFcompact, hnewU, hnewB, hnewfront, hnewrel, hnewprotect, hnewprotectB, hstripC, hfixed⟩

end PoincareConjecture.M76
