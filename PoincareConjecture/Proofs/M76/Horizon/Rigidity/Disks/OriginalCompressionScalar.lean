import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskCutDomainConstruction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalSignedDefiningFunction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalRelativeSigns
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLHalfspaceNeighborhood

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_compression_scalar
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {U : Set X} (hU : IsOpen U) (hSU : P.closedStrip ⊆ U)
    {old : X → ℝ} (hoc : Continuous old)
    (ho : ∀ i, LocallyPiecewiseAffineOn (old ∘ (e i).symm) (e i).target)
    (hpos : ∀ x, x ∈ interior R ↔ 0 < old x)
    (hzero : ∀ x, x ∈ frontier R ↔ old x = 0)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ x, |old x| ≤ r) :
    ∃ (g : X → ℝ) (N : Set X), IsCompact N ∧ PLDomain e N ∧
      P.closedStrip ⊆ interior N ∧ N ⊆ U ∧ Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g old (interior N)ᶜ ∧ (∀ x, |g x| ≤ r) ∧
      (∀ x, x ∈ interior P.cutCarrier ↔ 0 < g x) ∧
      (∀ x, x ∉ P.cutCarrier ↔ g x < 0) ∧
      g ⁻¹' {0} = (frontier R \ P.openStrip) ∪ P.endDisks := by
  obtain ⟨hK, hint, hfront, hoverlap, _, _⟩ := P.cut_geometry hR hopen
  have heK := P.plDomain_cut hR he hopen
  obtain ⟨f, hfc, hf, hsign⟩ := heK.exists_signed_defining_function hK
    isOpen_interior.isClosed_compl.isCompact
  obtain ⟨N, hN, hSN, hNU, hhalf⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible he.cover
      (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)) hU hSU
  have heN : PLDomain e N := ⟨he.cover, he.compatible, hN.isClosed, hhalf⟩
  have hUC : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hEC : P.endDisks ⊆ P.closedStrip := hoverlap.symm.subset.trans inter_subset_left
  have hnot (x : X) (hx : x ∈ (interior N)ᶜ) : x ∉ P.closedStrip :=
    fun h => hx (hSN h)
  have hiEq (x : X) (hx : x ∈ (interior N)ᶜ) :
      x ∈ interior P.cutCarrier ↔ x ∈ interior R := by
    rw [hint]
    exact and_iff_left (hnot x hx)
  have hfEq (x : X) (hx : x ∈ (interior N)ᶜ) :
      x ∈ frontier P.cutCarrier ↔ x ∈ frontier R := by
    rw [hfront]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact (hnot x hx (hEC h)).elim
    · exact fun h => Or.inl ⟨h, fun hs => hnot x hx (hUC hs)⟩
  obtain ⟨g, hgc, hg, heq, hgsign⟩ := heN.closed_exterior.exists_bounded_same_signs_relative
    isOpen_interior.isClosed_compl.isCompact hfc hoc hf ho
    (fun x hx => (hpos x).symm.trans ((hiEq x hx).symm.trans (hsign x).2.2.1))
    (fun x hx => (hzero x).symm.trans ((hfEq x hx).symm.trans (hsign x).2.1))
    hr (fun x _ => hbound x)
  refine ⟨g, N, hN, heN, hSN, hNU, hgc, hg, heq,
    fun x => (hgsign x).1, fun x => (hsign x).2.2.1.trans (hgsign x).2.1.symm,
    fun x => (hsign x).2.2.2.trans (hgsign x).2.2.2.symm, ?_⟩
  ext x
  change g x = 0 ↔ x ∈ (frontier R \ P.openStrip) ∪ P.endDisks
  exact (hgsign x).2.2.1.trans ((hsign x).2.1.symm.trans (Set.ext_iff.mp hfront x))

end PoincareConjecture.M76
