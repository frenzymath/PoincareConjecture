import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalEndpointExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_signed_half_face_map
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {s axis outer : Set X} {t Axis Outer : Set Y}
    (d : Bool → Set X) (D : Bool → Set Y) (a c : Bool → X) (A C : Bool → Y)
    (hs : IsFinitePLBallPair (ℝ × ℝ) s (axis ∪ outer))
    (ht : IsFinitePLBallPair (ℝ × ℝ) t (Axis ∪ Outer))
    (haxis : IsFinitePLBallPair ℝ axis {a false, a true})
    (hAxis : IsFinitePLBallPair ℝ Axis {A false, A true})
    (houter : IsFinitePLBallPair ℝ outer {a false, a true})
    (hOuter : IsFinitePLBallPair ℝ Outer {A false, A true})
    (hinter : axis ∩ outer = {a false, a true})
    (hInter : Axis ∩ Outer = {A false, A true})
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {a i, c i})
    (hD : ∀ i, IsFinitePLBallPair ℝ (D i) {A i, C i})
    (hdo : ∀ i, d i ⊆ outer) (hDO : ∀ i, D i ⊆ Outer)
    (ha : a false ≠ a true) (hA : A false ≠ A true)
    (hac : ∀ i, a i ≠ c i) (hAC : ∀ i, A i ≠ C i)
    (hdis : Disjoint (d false) (d true)) (hDis : Disjoint (D false) (D true))
    (z : axis ≃ₜ Axis) (hz : z.IsFinitePL)
    (hza : ∀ i, (z ⟨a i, haxis.1 (by cases i <;> simp)⟩ : Y) = A i)
    (e : ∀ i, d i ≃ₜ D i) (he : ∀ i, (e i).IsFinitePL)
    (hea : ∀ i, (e i ⟨a i, (hd i).1 (Or.inl rfl)⟩ : Y) = A i)
    (hec : ∀ i, (e i ⟨c i, (hd i).1 (Or.inr rfl)⟩ : Y) = C i) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ x : axis, (H ⟨x, hs.1 (Or.inl x.property)⟩ : Y) = z x) ∧
      (∀ i (x : d i),
        (H ⟨x, hs.1 (Or.inr (hdo i x.property))⟩ : Y) = e i x) ∧
      (∀ x : s, (x : X) ∈ axis ↔ (H x : Y) ∈ Axis) ∧
      (∀ x : s, (x : X) ∈ outer ↔ (H x : Y) ∈ Outer) ∧
      ∀ i (x : s), (x : X) ∈ d i ↔ (H x : Y) ∈ D i := by
  obtain ⟨o, ho, hkeep, hpieces, hoa⟩ :=
    houter.exists_extension_of_disjoint_end_intervals d D a c A C hOuter hd hD
      hdo hDO ha hA hac hAC hdis hDis e he hea hec
  have hziff (i : Bool) (x : axis) : (z x : Y) = A i ↔ (x : X) = a i := by
    constructor
    · intro hx
      exact congrArg Subtype.val (z.injective (Subtype.ext (hx.trans (hza i).symm)))
    · intro hx
      have hxeq : x = ⟨a i, haxis.1 (by cases i <;> simp)⟩ := Subtype.ext hx
      simpa only [hxeq] using hza i
  have hoiff (i : Bool) (x : outer) : (o x : Y) = A i ↔ (x : X) = a i := by
    constructor
    · intro hx
      exact congrArg Subtype.val (o.injective (Subtype.ext (hx.trans (hoa i).symm)))
    · intro hx
      have hxeq : x = ⟨a i, hdo i ((hd i).1 (Or.inl rfl))⟩ := Subtype.ext hx
      simpa only [hxeq] using hoa i
  have hoverlap (x : axis) : (x : X) ∈ outer ↔ (z x : Y) ∈ Outer := by
    have hx : (x : X) ∈ outer ↔ (x : X) ∈ ({a false, a true} : Set X) := by
      rw [← hinter]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (z x : Y) ∈ Outer ↔ (z x : Y) ∈ ({A false, A true} : Set Y) := by
      rw [← hInter]
      simp only [mem_inter_iff, (z x).property, true_and]
    rw [hx, hy]
    simp only [mem_insert_iff, mem_singleton_iff, hziff]
  have hagree (x : X) (hx : x ∈ axis) (hy : x ∈ outer) :
      (z ⟨x, hx⟩ : Y) = o ⟨x, hy⟩ := by
    rcases hinter.subset ⟨hx, hy⟩ with hxa | hxa
    · exact ((hziff false ⟨x, hx⟩).mpr hxa).trans ((hoiff false ⟨x, hy⟩).mpr hxa).symm
    · exact ((hziff true ⟨x, hx⟩).mpr hxa).trans ((hoiff true ⟨x, hy⟩).mpr hxa).symm
  obtain ⟨b, hb, hbaxis, hbouter⟩ := Homeomorph.exists_union_finitePL z o hz ho hoverlap hagree
  obtain ⟨H, hH, hHb, _⟩ := hs.exists_extension ht b hb
  have hHaxis (x : axis) : (H ⟨x, hs.1 (Or.inl x.property)⟩ : Y) = z x :=
    (congrArg (fun y : t => (y : Y)) (hHb ⟨x, Or.inl x.property⟩)).trans (hbaxis x)
  have hHouter (x : outer) : (H ⟨x, hs.1 (Or.inr x.property)⟩ : Y) = o x :=
    (congrArg (fun y : t => (y : Y)) (hHb ⟨x, Or.inr x.property⟩)).trans (hbouter x)
  have hHradius (i : Bool) (x : d i) :
      (H ⟨x, hs.1 (Or.inr (hdo i x.property))⟩ : Y) = e i x :=
    (hHouter ⟨x, hdo i x.property⟩).trans (congrArg (fun y : Outer => (y : Y)) (hkeep i x))
  exact ⟨H, hH, hHaxis, hHradius,
    H.mem_subset_iff_of_extension z (fun _ hx => hs.1 (Or.inl hx))
      (fun _ hx => ht.1 (Or.inl hx)) (fun x => Subtype.ext (hHaxis x)),
    H.mem_subset_iff_of_extension o (fun _ hx => hs.1 (Or.inr hx))
      (fun _ hx => ht.1 (Or.inr hx)) (fun x => Subtype.ext (hHouter x)),
    fun i => H.mem_subset_iff_of_extension (e i)
      (fun _ hx => hs.1 (Or.inr (hdo i hx)))
      (fun _ hx => ht.1 (Or.inr (hDO i hx))) (fun x => Subtype.ext (hHradius i x))⟩

end PoincareConjecture.M76.Dehn
