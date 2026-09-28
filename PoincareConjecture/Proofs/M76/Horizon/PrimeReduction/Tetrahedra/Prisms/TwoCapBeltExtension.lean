import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.FiniteRectangleBelt
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskPrismExtension

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PrismBelt

local notation "I" => Icc (0 : ℝ) 1

theorem exists_two_cap_prism_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N S B C T q r : Set E}
    (hN : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) N S)
    (hB : IsFinitePLBallPair (ℝ × ℝ) B q)
    (hcover : (B ∪ C) ∪ T = S) (hBC : Disjoint B C)
    (hBT : B ∩ T = q) (hCT : C ∩ T = r)
    (J : (q ×ˢ I : Set (E × ℝ)) ≃ₜ T) (hJ : J.IsFinitePL)
    (hJzero : ∀ (x : E) (hx : x ∈ q), (J ⟨(x, 0), hx, le_rfl, zero_le_one⟩ : E) = x)
    (hJbottom : ∀ x, (J x : E) ∈ q ↔ (x : E × ℝ).2 = 0)
    (hJtop : ∀ x, (J x : E) ∈ r ↔ (x : E × ℝ).2 = 1) :
    ∃ H : (B ×ˢ I : Set (E × ℝ)) ≃ₜ N, H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ B), (H ⟨(x, 0), hx, le_rfl, zero_le_one⟩ : E) = x) ∧
      (∀ x : (q ×ˢ I : Set (E × ℝ)),
        (H ⟨x, hB.1 x.property.1, x.property.2⟩ : E) = J x) ∧
      (∀ x, (H x : E) ∈ B ↔ (x : E × ℝ).2 = 0) ∧
      (∀ x, (H x : E) ∈ C ↔ (x : E × ℝ).2 = 1) ∧
      (∀ x, (H x : E) ∈ T ↔ (x : E × ℝ).1 ∈ q) := by
  classical
  have hBS : B ⊆ S := fun x hx => hcover.subset (Or.inl (Or.inl hx))
  have hCS : C ⊆ S := fun x hx => hcover.subset (Or.inl (Or.inr hx))
  have hTS : T ⊆ S := fun x hx => hcover.subset (Or.inr hx)
  have hJB (x : (q ×ˢ I : Set (E × ℝ))) : (J x : E) ∈ B ↔ (x : E × ℝ).2 = 0 := by
    constructor
    · exact fun hx => (hJbottom x).mp (hBT.subset ⟨hx, (J x).property⟩)
    · exact fun hx => hB.1 ((hJbottom x).mpr hx)
  have hout : (S \ B).Nonempty := by
    obtain ⟨n, P, _, _, hPq⟩ := hB.exists_polygon_boundary
    have hp : P 0 ∈ q := hPq ▸ P.vertex_mem_boundary 0
    let x : (q ×ˢ I : Set (E × ℝ)) := ⟨(P 0, 1), hp, zero_le_one, le_rfl⟩
    exact ⟨J x, hTS (J x).property, fun h => one_ne_zero ((hJB x).mp h)⟩
  obtain ⟨f, hf, hval⟩ := hJ
  have hfi : InjOn f (q ×ˢ I) := by
    intro x hx y hy he
    have hJe : J ⟨x, hx⟩ = J ⟨y, hy⟩ := Subtype.ext
      ((hval ⟨x, hx⟩).trans (he.trans (hval ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (J.injective hJe)
  obtain ⟨H, hH, hHzero, hHside, hHB, hHS⟩ := hN.exists_disk_prism_extension hB hBS hout f hf hfi
    (fun x hx => hval ⟨x, hx⟩ ▸ hTS (J ⟨x, hx⟩).property)
    (fun x hx => (hval ⟨(x, 0), hx, le_rfl, zero_le_one⟩).symm.trans (hJzero x hx))
    (fun x hx => (congrArg (fun y => y ∈ B) (hval ⟨x, hx⟩).symm).to_iff.trans (hJB ⟨x, hx⟩))
  have hside (x : (q ×ˢ I : Set (E × ℝ))) :
      (H ⟨x, hB.1 x.property.1, x.property.2⟩ : E) = J x :=
    (hHside x x.property).trans (hval x).symm
  have hHT (x : (B ×ˢ I : Set (E × ℝ))) : (H x : E) ∈ T ↔ (x : E × ℝ).1 ∈ q := by
    constructor
    · intro hx
      let y := J.symm ⟨H x, hx⟩
      have he : H ⟨y, hB.1 y.property.1, y.property.2⟩ = H x := Subtype.ext
        ((hside y).trans (congrArg Subtype.val (J.apply_symm_apply _)))
      have hxy := congrArg (fun z : (B ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).1) (H.injective he)
      exact hxy ▸ y.property.1
    · intro hx
      let y : (q ×ˢ I : Set (E × ℝ)) := ⟨x, hx, x.property.2⟩
      exact (hside y).symm ▸ (J y).property
  have hHC (x : (B ×ˢ I : Set (E × ℝ))) : (H x : E) ∈ C ↔ (x : E × ℝ).2 = 1 := by
    constructor
    · intro hx
      rcases (hHS x).mp (hCS hx) with hxq | ht
      · let y : (q ×ˢ I : Set (E × ℝ)) := ⟨x, hxq, x.property.2⟩
        have hxr : (H x : E) ∈ r := hCT.subset ⟨hx, (hHT x).mpr hxq⟩
        exact (hJtop y).mp ((hside y) ▸ hxr)
      · rcases ht with ht | ht
        · exact False.elim (disjoint_left.mp hBC ((hHB x).mpr ht) hx)
        · exact ht
    · intro ht
      have hxS : (H x : E) ∈ S := (hHS x).mpr (Or.inr (Or.inr ht))
      rcases hcover.symm.subset hxS with (hxB | hxC) | hxT
      · exact False.elim (zero_ne_one (((hHB x).mp hxB).symm.trans ht))
      · exact hxC
      · let y : (q ×ˢ I : Set (E × ℝ)) := ⟨x, (hHT x).mp hxT, x.property.2⟩
        have hyr := (hJtop y).mpr ht
        exact (hCT.symm.subset ((hside y).symm ▸ hyr)).1
  exact ⟨H, hH, hHzero, hside, hHB, hHC, hHT⟩

end PoincareConjecture.M76.PrismBelt
