import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.AffineEdgeFiberReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.SymmetricPrismTrim



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem prismTrim_agrees_on_equal_affine_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A B M L : Bool → Set E)
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (G : ∀ i, Square ≃ₜ M i) (hMB : ∀ i, M i ⊆ B i) (flip side : Bool → Bool)
    (hformula : ∀ i (u t : I),
      ((H i).symm ⟨G i ⟨(u,fiberFlip (flip i) t),u.property,(fiberFlip (flip i) t).property⟩,
        hMB i (G i _).property⟩ : E × ℝ) =
        ((G i ⟨(u,fiberFlip (flip i) 0),u.property,(fiberFlip (flip i) 0).property⟩ : E),(t : ℝ)))
    (hside : ∀ i t, (G i (sidePoint (side i) t) : E) =
      AffineMap.lineMap (G i (sidePoint (side i) 0) : E) (G i (sidePoint (side i) 1) : E) (t : ℝ))
    (hball : ∀ i, IsFinitePLBallPair ℝ (L i)
      {(G i (sidePoint (side i) 0) : E),(G i (sidePoint (side i) 1) : E)})
    (hL : L false = L true)
    (t s : I) (hpoint : (G false (sidePoint (side false) t) : E) =
      G true (sidePoint (side true) s)) :
    (G false (sidePoint (side false) t) : E) ∈ prismTrim (H false) ↔
      (G true (sidePoint (side true) s) : E) ∈ prismTrim (H true) := by
  have hball' := hball false
  rw [hL] at hball'
  have hpairs := hball'.boundary_eq_of_same_carrier (hball true)
  have hne : (G true (sidePoint (side true) 0) : E) ≠ G true (sidePoint (side true) 1) := by
    intro h
    have he := (G true).injective (Subtype.ext h)
    have ht := congrArg (fun z : Square => (z : ℝ × ℝ).2) he
    exact zero_ne_one ht
  have hline := (hside false t).symm.trans (hpoint.trans (hside true s))
  have hparam : (t : ℝ) = (s : ℝ) ∨ (t : ℝ) = 1-(s : ℝ) := by
    rcases pair_eq_pair_iff.mp hpairs with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · rw [h0,h1] at hline
      exact Or.inl (AffineMap.lineMap_injective ℝ hne hline)
    · rw [h0,h1,←AffineMap.lineMap_apply_one_sub] at hline
      have ht := AffineMap.lineMap_injective ℝ hne hline
      exact Or.inr (by linarith)
  have hmem (i : Bool) (v : I) :
      (G i (sidePoint (side i) v) : E) ∈ prismTrim (H i) ↔ (v : ℝ) ∈ Icc (1/4 : ℝ) (3/4) := by
    have hc : ((H i).symm ⟨G i (sidePoint (side i) v),hMB i (G i _).property⟩ : E × ℝ).2 =
        (fiberFlip (flip i) v : ℝ) := by
      cases hb : side i
      · exact congrArg Prod.snd (prism_inverse_on_global_rectangle (H i) (G i)
          (hMB i) (flip i) (hformula i) 0 v)
      · exact congrArg Prod.snd (prism_inverse_on_global_rectangle (H i) (G i)
          (hMB i) (flip i) (hformula i) 1 v)
    rw [mem_prismTrim_iff (H i) ⟨_,hMB i (G i _).property⟩,hc]
    exact fiberFlip_mem_middle_iff (flip i) v
  rw [hmem false t,hmem true s]
  rcases hparam with h | h
  · rw [h]
  · rw [h]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]

end PoincareConjecture.M76.PrismBelt

