import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubpolyhedronZeroSet
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLDiskAttachment










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def zeroSheet : E →ᴬ[ℝ] E × (ι → ℝ) :=
  (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)

noncomputable def separatedSheet (h : ι → E → ℝ) (i : ι) (x : E) : E × (ι → ℝ) :=
  (x, h i x • Pi.single i 1)

@[simp] theorem zeroSheet_apply (x : E) : zeroSheet (ι := ι) x = (x, 0) := rfl

theorem zeroSheet_injective : Function.Injective (zeroSheet (E := E) (ι := ι)) :=
  fun _ _ h ↦ congrArg Prod.fst h

theorem separatedSheet_injective (h : ι → E → ℝ) (i : ι) :
    Function.Injective (separatedSheet h i) := fun _ _ hxy ↦ congrArg Prod.fst hxy

theorem separatedSheet_finitePL (h : ι → E → ℝ) (i : ι) {u : Set E}
    (hh : FinitePiecewiseAffineOn (h i) u) :
    FinitePiecewiseAffineOn (separatedSheet h i) u := by
  obtain ⟨K, hK, hKu, hfaces⟩ := hh
  have hid : FinitePiecewiseAffineOn (id : E → E) u :=
    ⟨K, hK, hKu, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  have hh' : FinitePiecewiseAffineOn (fun x ↦ h i x • Pi.single i (1 : ℝ)) u :=
    (show FinitePiecewiseAffineOn (h i) u from ⟨K, hK, hKu, hfaces⟩).postcomp
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (Pi.single i 1 : ι → ℝ)).toContinuousAffineMap
  exact hid.prod_mk hh'

theorem separatedSheet_eq_zeroSheet_iff (h : ι → E → ℝ) (i : ι) (x y : E) :
    separatedSheet h i x = zeroSheet (ι := ι) y ↔ x = y ∧ h i x = 0 := by
  constructor
  · intro heq
    refine ⟨congrArg Prod.fst heq, ?_⟩
    have hh := congrArg (fun z : E × (ι → ℝ) ↦ z.2 i) heq
    simpa [separatedSheet] using hh
  · rintro ⟨rfl, hh⟩
    simp [separatedSheet, hh]

theorem separatedSheet_distinct_eq_iff (h : ι → E → ℝ) {i j : ι} (hij : i ≠ j) (x y : E) :
    separatedSheet h i x = separatedSheet h j y ↔ x = y ∧ h i x = 0 ∧ h j y = 0 := by
  constructor
  · intro heq
    have hi := congrArg (fun z : E × (ι → ℝ) ↦ z.2 i) heq
    have hj := congrArg (fun z : E × (ι → ℝ) ↦ z.2 j) heq
    exact ⟨congrArg Prod.fst heq, by simpa [separatedSheet, hij, hij.symm] using hi,
      by simpa [separatedSheet, hij, hij.symm] using hj.symm⟩
  · rintro ⟨rfl, hi, hj⟩
    simp [separatedSheet, hi, hj]


theorem exists_separating_disk_heights {u r d : ι → Set E} {a b : ι → E}
    (hu : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (u i) (r i))
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {a i, b i})
    (hdu : ∀ i, d i ⊆ u i) :
    ∃ h : ι → E → ℝ, (∀ i, FinitePiecewiseAffineOn (h i) (u i)) ∧
      ∀ i x, x ∈ u i → h i x ∈ Icc 0 1 ∧ (h i x = 0 ↔ x ∈ d i) := by
  classical
  have hone (i : ι) : ∃ h : E → ℝ, FinitePiecewiseAffineOn h (u i) ∧
      ∀ x ∈ u i, h x ∈ Icc 0 1 ∧ (h x = 0 ↔ x ∈ d i) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKu, _⟩, _⟩, _⟩ := hu i
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJd, _⟩, _⟩, _⟩ := hd i
    obtain ⟨f, hf, hzero⟩ := K.exists_finitePL_subpolyhedron_zero_set J hK hJ
      (hJd.trans_subset ((hdu i).trans hKu.symm.subset)) (by norm_num : (0 : ℝ) < 1)
    exact ⟨f, hKu ▸ hf, by simpa only [hKu, hJd] using hzero⟩
  choose h hh hzero using hone
  exact ⟨h, hh, hzero⟩

theorem separatedSheet_inter_base (h : ι → E → ℝ) (i : ι) {s u d : Set E}
    (hdu : d ⊆ u) (hds : d ⊆ s) (hzero : ∀ x ∈ u, h i x = 0 ↔ x ∈ d) :
    (zeroSheet (ι := ι) '' s) ∩ (separatedSheet h i '' u) = zeroSheet (ι := ι) '' d := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, hyz⟩, ⟨x, hx, hxz⟩⟩
    have hh := (separatedSheet_eq_zeroSheet_iff h i x y).mp (hxz.trans hyz.symm)
    exact ⟨x, (hzero x hx).mp hh.2, hh.1 ▸ hyz⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hds hx, rfl⟩, ⟨x, hdu hx,
      (separatedSheet_eq_zeroSheet_iff h i x x).mpr ⟨rfl, (hzero x (hdu hx)).mpr hx⟩⟩⟩

theorem separatedSheet_image_attachment (h : ι → E → ℝ) (i : ι) {u d : Set E}
    (hdu : d ⊆ u) (hzero : ∀ x ∈ u, h i x = 0 ↔ x ∈ d) :
    separatedSheet h i '' d = zeroSheet (ι := ι) '' d := by
  apply Set.image_congr
  intro x hx
  exact (separatedSheet_eq_zeroSheet_iff h i x x).mpr ⟨rfl, (hzero x (hdu hx)).mpr hx⟩

theorem separatedSheets_disjoint (h : ι → E → ℝ) {i j : ι} (hij : i ≠ j)
    {u v d e : Set E} (hde : Disjoint d e)
    (hi : ∀ x ∈ u, h i x = 0 ↔ x ∈ d) (hj : ∀ x ∈ v, h j x = 0 ↔ x ∈ e) :
    Disjoint (separatedSheet h i '' u) (separatedSheet h j '' v) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  obtain ⟨rfl, hxi, hyj⟩ := (separatedSheet_distinct_eq_iff h hij x y).mp (hxz.trans hyz.symm)
  exact Set.disjoint_left.mp hde ((hi _ hx).mp hxi) ((hj _ hy).mp hyj)

def separatedCarrier (h : ι → E → ℝ) (s : Set E) (u : ι → Set E) (T : Finset ι) :
    Set (E × (ι → ℝ)) := zeroSheet '' s ∪ ⋃ i ∈ T, separatedSheet h i '' u i

def separatedRim (h : ι → E → ℝ) (b : Set E) (r d : ι → Set E)
    (a z : ι → E) (T : Finset ι) : Set (E × (ι → ℝ)) :=
  (zeroSheet '' b ∪ ⋃ i ∈ T, separatedSheet h i '' r i) \
    ⋃ i ∈ T, ((zeroSheet '' d i) \ {zeroSheet (ι := ι) (a i), zeroSheet (ι := ι) (z i)})

theorem separatedCarrier_insert (h : ι → E → ℝ) (s : Set E) (u : ι → Set E)
    (T : Finset ι) (i : ι) :
    separatedCarrier h s u (insert i T) = separatedCarrier h s u T ∪ separatedSheet h i '' u i := by
  ext x
  simp only [separatedCarrier, mem_union, mem_iUnion, exists_prop, Finset.mem_insert]
  aesop

theorem separatedCarrier_inter_new (h : ι → E → ℝ) {s : Set E} {u d : ι → Set E}
    (hdu : ∀ i, d i ⊆ u i) (hds : ∀ i, d i ⊆ s)
    (hzero : ∀ i x, x ∈ u i → (h i x = 0 ↔ x ∈ d i))
    (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j)))
    (T : Finset ι) {i : ι} (hi : i ∉ T) :
    separatedCarrier h s u T ∩ (separatedSheet h i '' u i) = zeroSheet '' d i := by
  ext x
  constructor
  · rintro ⟨hx | hx, hxi⟩
    · exact (separatedSheet_inter_base h i (hdu i) (hds i) (hzero i)).subset ⟨hx, hxi⟩
    · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      have hji : j ≠ i := by intro heq; exact hi (heq ▸ hj)
      exact (Set.disjoint_left.mp
        (separatedSheets_disjoint h hji (hdis hji) (hzero j) (hzero i)) hxj hxi).elim
  · intro hx
    have hh := (separatedSheet_inter_base h i (hdu i) (hds i) (hzero i)).symm.subset hx
    exact ⟨Or.inl hh.1, hh.2⟩

theorem unused_attachment_subset_separatedRim (h : ι → E → ℝ) {b : Set E}
    {r d : ι → Set E} {a z : ι → E}
    (hdb : ∀ i, d i ⊆ b) (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j)))
    (T : Finset ι) {i : ι} (hi : i ∉ T) :
    zeroSheet (ι := ι) '' d i ⊆ separatedRim h b r d a z T := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨Or.inl ⟨y, hdb i hy, rfl⟩, ?_⟩
  intro hx
  obtain ⟨j, hj, ⟨w, hw, hwy⟩, _⟩ := mem_iUnion₂.mp hx
  have hji : j ≠ i := by intro heq; exact hi (heq ▸ hj)
  have hwy' : w = y := congrArg Prod.fst hwy
  subst w
  exact Set.disjoint_left.mp (hdis hji) hw hy

theorem separatedRim_insert (h : ι → E → ℝ) {b : Set E} {u r d : ι → Set E} {a z : ι → E}
    (hru : ∀ i, r i ⊆ u i) (hdu : ∀ i, d i ⊆ u i)
    (hzero : ∀ i x, x ∈ u i → (h i x = 0 ↔ x ∈ d i))
    (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j)))
    (T : Finset ι) {i : ι} (hi : i ∉ T) :
    separatedRim h b r d a z (insert i T) =
      (separatedRim h b r d a z T ∪ separatedSheet h i '' r i) \
        ((zeroSheet '' d i) \ {zeroSheet (ι := ι) (a i), zeroSheet (ι := ι) (z i)}) := by
  have havoid {x : E × (ι → ℝ)} (hx : x ∈ separatedSheet h i '' r i) :
      x ∉ ⋃ j ∈ T, ((zeroSheet '' d j) \
        {zeroSheet (ι := ι) (a j), zeroSheet (ι := ι) (z j)}) := by
    intro hbad
    obtain ⟨j, hj, hxj, _⟩ := mem_iUnion₂.mp hbad
    have hij : i ≠ j := by intro heq; exact hi (heq.symm ▸ hj)
    have hxju : x ∈ separatedSheet h j '' u j := by
      rw [← separatedSheet_image_attachment h j (hdu j) (hzero j)] at hxj
      exact image_mono (hdu j) hxj
    exact Set.disjoint_left.mp
      (separatedSheets_disjoint h hij (hdis hij) (hzero i) (hzero j))
      (image_mono (hru i) hx) hxju
  ext x
  have hsplit (A : ι → Set (E × (ι → ℝ))) :
      x ∈ (⋃ j ∈ insert i T, A j) ↔ x ∈ A i ∨ x ∈ ⋃ j ∈ T, A j := by
    simp only [mem_iUnion, exists_prop, Finset.mem_insert]
    aesop
  simp only [separatedRim, mem_sdiff, mem_union, hsplit]
  have ha := @havoid x
  tauto




theorem separated_disks_isFinitePLBallPair (h : ι → E → ℝ)
    {s b : Set E} {u r d : ι → Set E} {a z : ι → E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s b)
    (hu : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (u i) (r i))
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {a i, z i})
    (hdb : ∀ i, d i ⊆ b) (hdr : ∀ i, d i ⊆ r i) (haz : ∀ i, a i ≠ z i)
    (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j)))
    (hh : ∀ i, FinitePiecewiseAffineOn (h i) (u i))
    (hzero : ∀ i x, x ∈ u i → (h i x = 0 ↔ x ∈ d i)) (T : Finset ι) :
    IsFinitePLBallPair (ℝ × ℝ) (separatedCarrier h s u T) (separatedRim h b r d a z T) := by
  have hdu : ∀ i, d i ⊆ u i := fun i ↦ (hdr i).trans (hu i).1
  have hds : ∀ i, d i ⊆ s := fun i ↦ (hdb i).trans hs.1
  induction T using Finset.induction_on with
  | empty =>
    simpa only [separatedCarrier, separatedRim, Finset.notMem_empty,
      iUnion_of_empty, iUnion_empty, union_empty, sdiff_empty] using
      hs.affine_image (zeroSheet (ι := ι)) zeroSheet_injective.injOn
  | @insert i T hi ih =>
    have hui := (hu i).image (separatedSheet_finitePL h i (hh i))
      (separatedSheet_injective h i).injOn
    have hdi : IsFinitePLBallPair ℝ (zeroSheet (ι := ι) '' d i)
        {zeroSheet (ι := ι) (a i), zeroSheet (ι := ι) (z i)} := by
      simpa only [image_pair] using (hd i).affine_image
        (zeroSheet (ι := ι)) zeroSheet_injective.injOn
    have hdc : zeroSheet (ι := ι) '' d i ⊆ separatedSheet h i '' r i := by
      rw [← separatedSheet_image_attachment h i (hdu i) (hzero i)]
      exact image_mono (hdr i)
    have hresult := ih.union_of_boundary_interval hui hdi
      (unused_attachment_subset_separatedRim h hdb hdis T hi) hdc
      (fun heq ↦ haz i (zeroSheet_injective heq))
      (separatedCarrier_inter_new h hdu hds hzero hdis T hi)
    rw [separatedCarrier_insert,
      separatedRim_insert h (fun i ↦ (hu i).1) hdu hzero hdis T hi]
    exact hresult

theorem projection_separatedCarrier (h : ι → E → ℝ) (s : Set E)
    (u : ι → Set E) (T : Finset ι) :
    Prod.fst '' separatedCarrier h s u T = s ∪ ⋃ i ∈ T, u i := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨y, hy, rfl⟩ | hp
    · exact Or.inl hy
    · obtain ⟨i, hi, y, hy, rfl⟩ := mem_iUnion₂.mp hp
      exact Or.inr (mem_iUnion₂.mpr ⟨i, hi, hy⟩)
  · rintro (hx | hx)
    · exact ⟨zeroSheet (ι := ι) x, Or.inl ⟨x, hx, rfl⟩, rfl⟩
    · obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      exact ⟨separatedSheet h i x, Or.inr (mem_iUnion₂.mpr ⟨i, hi, x, hx, rfl⟩), rfl⟩



theorem exists_separated_disks
    {s b : Set E} {u r d : ι → Set E} {a z : ι → E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s b)
    (hu : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (u i) (r i))
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {a i, z i})
    (hdb : ∀ i, d i ⊆ b) (hdr : ∀ i, d i ⊆ r i) (haz : ∀ i, a i ≠ z i)
    (hdis : Pairwise (fun i j ↦ Disjoint (d i) (d j))) :
    ∃ h : ι → E → ℝ,
      (∀ i, FinitePiecewiseAffineOn (h i) (u i)) ∧
      (∀ i x, x ∈ u i → h i x ∈ Icc 0 1 ∧ (h i x = 0 ↔ x ∈ d i)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (separatedCarrier h s u Finset.univ)
        (separatedRim h b r d a z Finset.univ) ∧
      FinitePiecewiseAffineOn (Prod.fst : E × (ι → ℝ) → E)
        (separatedCarrier h s u Finset.univ) ∧
      Prod.fst '' separatedCarrier h s u Finset.univ = s ∪ ⋃ i, u i := by
  obtain ⟨h, hh, hz⟩ := exists_separating_disk_heights hu hd (fun i ↦ (hdr i).trans (hu i).1)
  have hdisk := separated_disks_isFinitePLBallPair h hs hu hd hdb hdr haz hdis hh
    (fun i x hx ↦ (hz i x hx).2) Finset.univ
  have htri := hdisk
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨C, hC, hCs, _⟩, _⟩, _⟩ := htri
  refine ⟨h, hh, hz, hdisk,
    ⟨C, hC, hCs, C.affineOnFaces_affine (ContinuousLinearMap.fst ℝ E (ι → ℝ)).toContinuousAffineMap⟩, ?_⟩
  simpa only [Finset.mem_univ, iUnion_true] using projection_separatedCarrier h s u Finset.univ

end PoincareConjecture.M76.OriginalTriangleCopies
