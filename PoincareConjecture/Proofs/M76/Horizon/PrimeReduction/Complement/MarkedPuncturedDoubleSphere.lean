import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.MarkedDoubleBallSphere
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.MarkedCapExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation

set_option autoImplicit false

open Set Metric Geometry

namespace Set

local notation "V3" => (Fin 3 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.isOpen_nested_ball_rim_complement
    {d q a r : Set E} (hd : IsFinitePLBallPair V3 d q)
    (ha : IsFinitePLBallPair V3 a r) (had : a ⊆ d) :
    IsOpen ((Subtype.val : d → E) ⁻¹' (a \ r)) := by
  obtain ⟨e, he, _⟩ := hd.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨f, hf, hval⟩ := he
  have hfi : InjOn f d := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have hfa := ha.image_of_subset hf had hfi
  have hopen : IsOpen ((f '' a) \ (f '' r)) := by
    rw [← hfa.interior_eq_sdiff_of_finrank_eq rfl]
    exact isOpen_interior
  have heq : (fun x : d => (e x : V3)) ⁻¹' ((f '' a) \ (f '' r)) =
      (Subtype.val : d → E) ⁻¹' (a \ r) := by
    ext x
    have hm (s : Set E) (hs : s ⊆ d) : (e x : V3) ∈ f '' s ↔ (x : E) ∈ s := by
      rw [hval x]
      constructor
      · rintro ⟨y, hy, hyx⟩
        exact hfi (hs hy) x.property hyx ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    exact and_congr (hm a had) (not_congr (hm r (ha.1.trans had)))
  rw [← heq]
  exact hopen.preimage (continuous_subtype_val.comp e.continuous)

theorem IsFinitePLBallPair.isOpen_double_ball_hole
    {b d q a r : Set E} (hb : IsFinitePLBallPair V3 b q)
    (hd : IsFinitePLBallPair V3 d q) (hinter : b ∩ d = q)
    (ha : IsFinitePLBallPair V3 a r) (had : a ⊆ d \ q) :
    IsOpen ((Subtype.val : (b ∪ d : Set E) → E) ⁻¹' (a \ r)) := by
  obtain ⟨U, hU, hUd⟩ := isOpen_induced_iff.mp
    (hd.isOpen_nested_ball_rim_complement ha (had.trans sdiff_subset))
  have heq : (Subtype.val : (b ∪ d : Set E) → E) ⁻¹' (U \ b) =
      (Subtype.val : (b ∪ d : Set E) → E) ⁻¹' (a \ r) := by
    ext x
    constructor
    · rintro ⟨hxU, hxb⟩
      have hxd : (x : E) ∈ d := x.property.resolve_left hxb
      exact (Set.ext_iff.mp hUd ⟨x, hxd⟩).mp hxU
    · intro hx
      have hxd := (had hx.1).1
      refine ⟨(Set.ext_iff.mp hUd ⟨x, hxd⟩).mpr hx, ?_⟩
      intro hxb
      exact (had hx.1).2 (hinter ▸ And.intro hxb hxd)
  rw [← heq]
  exact (hU.sdiff hb.isCompact.isClosed).preimage continuous_subtype_val

theorem IsFinitePLBallPair.isClosed_punctured_double
    {ι : Type*} {b d q : Set E} (hb : IsFinitePLBallPair V3 b q)
    (hd : IsFinitePLBallPair V3 d q) (hinter : b ∩ d = q)
    (a r : ι → Set E) (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (had : ∀ i, a i ⊆ d \ q) :
    IsClosed ((b ∪ d) \ ⋃ i, a i \ r i) := by
  have hopen : IsOpen ((Subtype.val : (b ∪ d : Set E) → E) ⁻¹'
      (⋃ i, a i \ r i)) := by
    rw [preimage_iUnion]
    exact isOpen_iUnion fun i => hb.isOpen_double_ball_hole hd hinter (ha i) (had i)
  have himage : (Subtype.val : (b ∪ d : Set E) → E) ''
      (((Subtype.val : (b ∪ d : Set E) → E) ⁻¹' (⋃ i, a i \ r i))ᶜ) =
        (b ∪ d) \ ⋃ i, a i \ r i := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [← himage]
  exact (hb.isCompact.isClosed.union hd.isCompact.isClosed).isClosedMap_subtype_val
    _ hopen.isClosed_compl

open Geometry.CubicalThreeSphere

theorem IsFinitePLBallPair.exists_marked_punctured_double_sphere
    {ι : Type*} [Finite ι] {b d q : Set E}
    (hb : IsFinitePLBallPair V3 b q) (hd : IsFinitePLBallPair V3 d q)
    (hinter : b ∩ d = q) (a r : ι → Set E)
    (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (had : ∀ i, a i ⊆ d \ q)
    (hdis : Pairwise fun i j => Disjoint (a i) (a j)) :
    ∃ (f : E → Fin 4 → ℝ) (H : (b ∪ d : Set E) ≃ₜ sphere),
      H.IsFinitePL ∧
      (∀ x : d, (H ⟨x, Or.inr x.property⟩ : Fin 4 → ℝ) = f x) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ b ↔ (H x : Fin 4 → ℝ) ∈ lower) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ d ↔ (H x : Fin 4 → ℝ) ∈ upper) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ q ↔ (H x : Fin 4 → ℝ) ∈ seam) ∧
      (∀ i, IsFinitePLBallPair V3 (f '' a i) (f '' r i)) ∧
      (∀ i, f '' a i ⊆ upper \ seam) ∧
      Pairwise (fun i j => Disjoint (f '' a i) (f '' a j)) ∧
      let p := (b ∪ d) \ ⋃ i, a i \ r i
      let P := sphere \ ⋃ i, (f '' a i) \ (f '' r i)
      ∃ (L : SimplicialComplex ℝ E) (F : p ≃ₜ P),
        L.faces.Finite ∧ L.space = p ∧ F.IsFinitePL ∧
        (∀ x : p, (F x : Fin 4 → ℝ) = H ⟨x, x.property.1⟩) ∧
        (∀ x : p, (x : E) ∈ d → (F x : Fin 4 → ℝ) = f x) ∧
        (∀ i (x : p), (x : E) ∈ r i ↔ (F x : Fin 4 → ℝ) ∈ f '' r i) ∧
        (∀ i, (fun x : p => (F x : Fin 4 → ℝ)) ''
          ((Subtype.val : p → E) ⁻¹' r i) = f '' r i) := by
  obtain ⟨e, he, hmem⟩ := hd.exists_homeomorph upper_ball
  have hecopy := he
  obtain ⟨f, _, hval⟩ := hecopy
  obtain ⟨H, hH, hkeep, hHb, hHd, hballs, hdisImages, _,
    F, hFH, hFd, hFr, hFri, hFPL⟩ :=
    hb.exists_marked_cap_extension lower_ball hinter lower_inter_upper
      e he hmem f hval a r ha (fun i => (had i).trans sdiff_subset) hdis
  have hHcopy := hH
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hHcopy
  have haK (i : ι) : a i ⊆ K.space :=
    (had i).trans (sdiff_subset.trans (subset_union_right.trans hKs.symm.subset))
  have hclosed : IsClosed (K.space \ ⋃ i, a i \ r i) := by
    rw [hKs]
    exact hb.isClosed_punctured_double hd hinter a r ha had
  obtain ⟨_, L, _, _, _, _, _, hL, hLs, _, _⟩ :=
    K.exists_finite_closed_punctured_ball_carrier hK a r ha haK hdis hclosed
  have hLspace : L.space = (b ∪ d) \ ⋃ i, a i \ r i := by
    simpa only [hKs] using hLs
  have hqH (x : (b ∪ d : Set E)) : (x : E) ∈ q ↔
      (H x : Fin 4 → ℝ) ∈ seam := by
    rw [← hinter, ← lower_inter_upper]
    exact and_congr (hHb x) (hHd x)
  have hhole (i : ι) : f '' a i ⊆ upper \ seam := by
    rintro y ⟨x, hx, rfl⟩
    have hxd := (had i hx).1
    have hfx := hval ⟨x, hxd⟩
    refine ⟨hfx ▸ (e ⟨x, hxd⟩).property, ?_⟩
    intro hs
    exact (had i hx).2 ((hmem ⟨x, hxd⟩).mpr (hfx.symm ▸ hs))
  rw [← lower_union_upper]
  exact ⟨f, H, hH, hkeep, hHb, hHd, hqH, hballs, hhole, hdisImages,
    L, F, hL, hLspace, hFPL L hL hLspace, hFH, hFd, hFr, hFri⟩

end Set
