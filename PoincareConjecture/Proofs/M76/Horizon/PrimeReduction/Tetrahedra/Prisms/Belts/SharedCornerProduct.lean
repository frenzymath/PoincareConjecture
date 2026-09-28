import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.FiniteRectangleBelt

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_belt_product_of_shared_cap_corners
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι]
    (M W Z : ι → Set E) (L : ι → Bool → Set E) (p q : ι → Bool → E)
    (A B : Set E)
    (hL : ∀ i b, IsFinitePLBallPair ℝ (L i b) {p i b,q i b})
    (hpq : ∀ i b, p i b ≠ q i b)
    (hM : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (M i)
      ((W i ∪ Z i) ∪ (L i false ∪ L i true)))
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {p i false,p i true})
    (hZ : ∀ i, IsFinitePLBallPair ℝ (Z i) {q i false,q i true})
    (hWZ : ∀ i, Disjoint (W i) (Z i))
    (hLR : ∀ i, Disjoint (L i false) (L i true))
    (hWL : ∀ i b, W i ∩ L i b = {p i b})
    (hZL : ∀ i b, Z i ∩ L i b = {q i b})
    (hAL : ∀ i b, A ∩ L i b = {p i b})
    (hBL : ∀ i b, B ∩ L i b = {q i b})
    (hcontact : ∀ i j, i ≠ j → (M i ∩ M j).Nonempty →
      ∃ b c, L i b = L j c ∧ M i ∩ M j = L i b) :
    ∃ H : ((⋃ i, W i) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i), H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ ⋃ i, W i),
        (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
      (∀ i x, (H x : E) ∈ M i ↔ (x : E × ℝ).1 ∈ W i) ∧
      (∀ x, (H x : E) ∈ (⋃ i, W i) ↔ (x : E × ℝ).2 = 0) ∧
      (∀ x, (H x : E) ∈ (⋃ i, Z i) ↔ (x : E × ℝ).2 = 1) := by
  classical
  let Edge := {s : Set E // ∃ i b, s = L i b}
  let ends (i : ι) (b : Bool) : Edge := ⟨L i b,i,b,rfl⟩
  choose ri rb hr using fun k : Edge => k.2
  let P (k : Edge) := p (ri k) (rb k)
  let Q (k : Edge) := q (ri k) (rb k)
  have hP (i : ι) (b : Bool) : P (ends i b) = p i b := by
    have hs : L (ri (ends i b)) (rb (ends i b)) = L i b := (hr _).symm
    have hp := hAL (ri (ends i b)) (rb (ends i b))
    rw [hs] at hp
    exact singleton_injective (hp.symm.trans (hAL i b))
  have hQ (i : ι) (b : Bool) : Q (ends i b) = q i b := by
    have hs : L (ri (ends i b)) (rb (ends i b)) = L i b := (hr _).symm
    have hq := hBL (ri (ends i b)) (rb (ends i b))
    rw [hs] at hq
    exact singleton_injective (hq.symm.trans (hBL i b))
  apply exists_finite_rectangular_belt_product M W Z (fun k : Edge => k.1) ends P Q
  · intro k
    exact (hr k).symm ▸ hL (ri k) (rb k)
  · intro k
    exact hpq (ri k) (rb k)
  · exact hM
  · intro i
    simpa only [hP] using hW i
  · intro i
    simpa only [hQ] using hZ i
  · exact hWZ
  · exact hLR
  · intro i b
    simpa only [hP] using hWL i b
  · intro i b
    simpa only [hQ] using hZL i b
  · intro i j hij hmeet
    obtain ⟨b,c,hside,hinter⟩ := hcontact i j hij hmeet
    exact ⟨b,c,Subtype.ext hside,hinter⟩

end PoincareConjecture.M76.PrismBelt
