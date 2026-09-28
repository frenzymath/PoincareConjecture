import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.SeparatedDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
theorem separatedCarrier_projection_fiber
    (h : ι → E → ℝ) (s : Set E) (u : ι → Set E) (T : Finset ι) (x : E) :
    separatedCarrier h s u T ∩ Prod.fst ⁻¹' {x} =
      (if x ∈ s then {zeroSheet (ι := ι) x} else ∅) ∪
        ⋃ i ∈ T, if x ∈ u i then {separatedSheet h i x} else ∅ := by
  classical
  ext p
  constructor
  · rintro ⟨hp | hp, hpx⟩
    · obtain ⟨y, hy, rfl⟩ := hp
      have hyx : y = x := hpx
      subst y
      exact Or.inl (by simp [hy])
    · obtain ⟨i, hi, y, hy, rfl⟩ := mem_iUnion₂.mp hp
      have hyx : y = x := hpx
      subst y
      exact Or.inr (mem_iUnion₂.mpr ⟨i, hi, by simp [hy]⟩)
  · rintro (hp | hp)
    · split_ifs at hp with hx
      · have hp' : p = zeroSheet (ι := ι) x := hp
        subst p
        exact ⟨Or.inl ⟨x, hx, rfl⟩, rfl⟩
      · exact hp.elim
    · obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
      split_ifs at hp with hx
      · have hp' : p = separatedSheet h i x := hp
        subst p
        exact ⟨Or.inr (mem_iUnion₂.mpr ⟨i, hi, x, hx, rfl⟩), rfl⟩
      · exact hp.elim

theorem zeroSheet_mem_separatedRim_iff (h : ι → E → ℝ)
    {b : Set E} {r d : ι → Set E} {a z : ι → E} (T : Finset ι)
    {x : E} (hx : x ∈ b) :
    zeroSheet (ι := ι) x ∈ separatedRim h b r d a z T ↔
      ∀ i ∈ T, x ∈ d i → x = a i ∨ x = z i := by
  constructor
  · intro hp i hi hxi
    by_contra hne
    apply hp.2
    refine mem_iUnion₂.mpr ⟨i, hi, ⟨x, hxi, rfl⟩, ?_⟩
    rintro (heq | heq)
    · exact hne (Or.inl (zeroSheet_injective heq))
    · exact hne (Or.inr (zeroSheet_injective heq))
  · intro hall
    refine ⟨Or.inl ⟨x, hx, rfl⟩, ?_⟩
    intro hp
    obtain ⟨i, hi, ⟨y, hy, hyx⟩, hne⟩ := mem_iUnion₂.mp hp
    have hyx' := zeroSheet_injective hyx
    subst y
    rcases hall i hi hy with heq | heq
    · exact hne (Or.inl (congrArg (zeroSheet (ι := ι)) heq))
    · exact hne (Or.inr (congrArg (zeroSheet (ι := ι)) heq))

theorem separatedSheet_mem_separatedRim_iff (h : ι → E → ℝ)
    {b : Set E} {u r d : ι → Set E} {a z : ι → E}
    (hru : ∀ i, r i ⊆ u i)
    (hzero : ∀ i x, x ∈ u i → (h i x = 0 ↔ x ∈ d i))
    (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j)))
    (T : Finset ι) {i : ι} (hi : i ∈ T) {x : E} (hx : x ∈ r i) :
    separatedSheet h i x ∈ separatedRim h b r d a z T ↔
      x ∈ d i → x = a i ∨ x = z i := by
  constructor
  · intro hp hxd
    have heq := (separatedSheet_eq_zeroSheet_iff h i x x).mpr
      ⟨rfl, (hzero i x (hru i hx)).mpr hxd⟩
    by_contra hne
    apply hp.2
    refine mem_iUnion₂.mpr ⟨i, hi, ⟨x, hxd, heq.symm⟩, ?_⟩
    rintro (ha | hz)
    · exact hne (Or.inl (congrArg Prod.fst ha))
    · exact hne (Or.inr (congrArg Prod.fst hz))
  · intro hall
    refine ⟨Or.inr (mem_iUnion₂.mpr ⟨i, hi, x, hx, rfl⟩), ?_⟩
    intro hp
    obtain ⟨j, hj, ⟨y, hy, hyx⟩, hne⟩ := mem_iUnion₂.mp hp
    obtain ⟨hxy, hzero'⟩ := (separatedSheet_eq_zeroSheet_iff h i x y).mp hyx.symm
    subst y
    have hxd := (hzero i x (hru i hx)).mp hzero'
    by_cases hij : i = j
    · subst j
      rcases hall hxd with hxa | hxz
      · exact hne (Or.inl (hyx.symm.trans (congrArg (zeroSheet (ι := ι)) hxa)))
      · exact hne (Or.inr (hyx.symm.trans (congrArg (zeroSheet (ι := ι)) hxz)))
    · exact Set.disjoint_left.mp (hdis hij) hxd hy

theorem separatedSheet_inter_separatedRim (h : ι → E → ℝ)
    {b : Set E} {u r d : ι → Set E} {a z : ι → E}
    (hru : ∀ i, r i ⊆ u i)
    (hzero : ∀ i x, x ∈ u i → (h i x = 0 ↔ x ∈ d i))
    (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j)))
    (T : Finset ι) {i : ι} (hi : i ∈ T) :
    separatedSheet h i '' r i ∩ separatedRim h b r d a z T =
      separatedSheet h i '' (r i \ (d i \ {a i, z i})) := by
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hr⟩
    have hh := (separatedSheet_mem_separatedRim_iff h hru hzero hdis T hi hx).mp hr
    exact ⟨x, ⟨hx, fun hbad ↦ hbad.2 (hh hbad.1)⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩,
      (separatedSheet_mem_separatedRim_iff h hru hzero hdis T hi hx.1).mpr ?_⟩
    intro hxd
    by_contra hne
    exact hx.2 ⟨hxd, hne⟩

theorem retained_sheet_trace_subset_separatedRim (h : ι → E → ℝ)
    {b : Set E} {u r d : ι → Set E} {a z : ι → E}
    (hru : ∀ i, r i ⊆ u i)
    (hzero : ∀ i x, x ∈ u i → (h i x = 0 ↔ x ∈ d i))
    (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j)))
    (T : Finset ι) {i : ι} (hi : i ∈ T) {c : Set E}
    (hcr : c ⊆ r i) (hcd : c ∩ d i ⊆ {a i, z i}) :
    separatedSheet h i '' c ⊆ separatedRim h b r d a z T := by
  rintro p ⟨x, hx, rfl⟩
  exact (separatedSheet_mem_separatedRim_iff h hru hzero hdis T hi (hcr hx)).mpr
    (fun hxd ↦ hcd ⟨hx, hxd⟩)

noncomputable def separatedSourceSheet (h : ι → E → ℝ) : Option ι → E → E × (ι → ℝ)
  | none => zeroSheet
  | some i => separatedSheet h i

def separatedSourcePiece (s : Set E) (u : ι → Set E) : Option ι → Set E
  | none => s
  | some i => u i

def separatedSheetActive (T : Finset ι) : Option ι → Prop
  | none => True
  | some i => i ∈ T

theorem mem_separatedCarrier_iff_sheet (h : ι → E → ℝ)
    (s : Set E) (u : ι → Set E) (T : Finset ι) (p : E × (ι → ℝ)) :
    p ∈ separatedCarrier h s u T ↔
      ∃ i : Option ι, separatedSheetActive T i ∧
        p.1 ∈ separatedSourcePiece s u i ∧ p = separatedSourceSheet h i p.1 := by
  constructor
  · rintro (⟨x, hx, rfl⟩ | hp)
    · exact ⟨none, trivial, hx, rfl⟩
    · obtain ⟨i, hi, x, hx, rfl⟩ := mem_iUnion₂.mp hp
      exact ⟨some i, hi, hx, rfl⟩
  · rintro ⟨i, hi, hx, hp⟩
    rcases i with _ | i
    · exact Or.inl ⟨p.1, hx, hp.symm⟩
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, hi, p.1, hx, hp.symm⟩)



theorem separated_projection_eq_iff_source_overlap (h : ι → E → ℝ)
    (s : Set E) (u : ι → Set E) (T : Finset ι)
    (p q : separatedCarrier h s u T) :
    p.val.1 = q.val.1 ↔
      ∃ i j : Option ι, separatedSheetActive T i ∧ separatedSheetActive T j ∧
        ∃ x ∈ separatedSourcePiece s u i ∩ separatedSourcePiece s u j,
          p.val = separatedSourceSheet h i x ∧ q.val = separatedSourceSheet h j x := by
  constructor
  · intro hpq
    obtain ⟨i, hi, hpi, hp⟩ := (mem_separatedCarrier_iff_sheet h s u T p.val).mp p.property
    obtain ⟨j, hj, hqj, hq⟩ := (mem_separatedCarrier_iff_sheet h s u T q.val).mp q.property
    exact ⟨i, j, hi, hj, p.val.1, ⟨hpi, hpq.symm ▸ hqj⟩, hp, hpq.symm ▸ hq⟩
  · rintro ⟨i, j, _, _, x, _, hp, hq⟩
    rw [hp, hq]
    rcases i with _ | i <;> rcases j with _ | j <;> rfl

def separatedSourceSetoid (h : ι → E → ℝ) (s : Set E) (u : ι → Set E) (T : Finset ι) :
    Setoid (separatedCarrier h s u T) := Setoid.ker (fun p ↦ p.val.1)

def separatedSourceProjection (h : ι → E → ℝ) (s : Set E) (u : ι → Set E) (T : Finset ι)
    (p : separatedCarrier h s u T) : ↥(s ∪ ⋃ i ∈ T, u i) :=
  ⟨p.val.1, (projection_separatedCarrier h s u T).subset ⟨p.val, p.property, rfl⟩⟩

theorem exists_separatedSourceQuotient_homeomorph (h : ι → E → ℝ)
    (s : Set E) (u : ι → Set E) (T : Finset ι)
    (hc : IsCompact (separatedCarrier h s u T)) :
    ∃ f : Quotient (separatedSourceSetoid h s u T) ≃ₜ ↥(s ∪ ⋃ i ∈ T, u i),
      ∀ p : separatedCarrier h s u T,
        f (Quotient.mk (separatedSourceSetoid h s u T) p) =
          separatedSourceProjection h s u T p := by
  let : CompactSpace (separatedCarrier h s u T) := isCompact_iff_compactSpace.mp hc
  let q : Quotient (separatedSourceSetoid h s u T) → ↥(s ∪ ⋃ i ∈ T, u i) :=
    Quotient.lift (separatedSourceProjection h s u T) (fun _ _ hpq ↦ Subtype.ext hpq)
  have hsurj : Function.Surjective q := by
    intro x
    obtain ⟨p, hp, hpx⟩ := (projection_separatedCarrier h s u T).symm.subset x.property
    exact ⟨Quotient.mk (separatedSourceSetoid h s u T) ⟨p, hp⟩, Subtype.ext hpx⟩
  have hinj : Function.Injective q := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ p =>
      induction y using Quotient.inductionOn with
      | _ r => exact Quotient.sound (congrArg Subtype.val hxy)
  have hcont : Continuous q := by
    apply (@isQuotientMap_quotient_mk' (separatedCarrier h s u T) _
      (separatedSourceSetoid h s u T)).continuous_iff.mpr
    exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
  let e : Quotient (separatedSourceSetoid h s u T) ≃ ↥(s ∪ ⋃ i ∈ T, u i) :=
    Equiv.ofBijective q ⟨hinj, hsurj⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hcont, fun _ ↦ rfl⟩

end PoincareConjecture.M76.OriginalTriangleCopies
