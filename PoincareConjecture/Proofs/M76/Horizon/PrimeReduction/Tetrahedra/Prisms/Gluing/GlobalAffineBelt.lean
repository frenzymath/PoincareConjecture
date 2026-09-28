import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalMatchedBelt
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalOriginalFaceCharts










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_global_affine_side_belt
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (M W Z : ι → Set E) (L : ι → Bool → Set E) (p q : ι → Bool → E)
    (A B : Set E) (hsegment : ∀ i b, L i b = segment ℝ (p i b) (q i b))
    (hpq : ∀ i b, p i b ≠ q i b)
    (hAL : ∀ i b, A ∩ L i b = {p i b}) (hBL : ∀ i b, B ∩ L i b = {q i b})
    (hWsub : ∀ i, W i ⊆ M i) (hZsub : ∀ i, Z i ⊆ M i)
    (G : ∀ i, Square ≃ₜ M i) (hG : ∀ i, (G i).IsFinitePL)
    (hGW : ∀ i z, (G i z : E) ∈ W i ↔ (z : ℝ × ℝ).2 = 0)
    (hGZ : ∀ i z, (G i z : E) ∈ Z i ↔ (z : ℝ × ℝ).2 = 1)
    (hside : ∀ i b t, (G i (sidePoint b t) : E) = AffineMap.lineMap (p i b) (q i b) (t : ℝ))
    (hcontact : ∀ i k, i ≠ k → (M i ∩ M k).Nonempty →
      ∃ b c, L i b = L k c ∧ M i ∩ M k = L i b) :
    ∃ H : ((⋃ i, W i) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i), H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ ⋃ i, W i),
        (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
      (∀ i z, (H z : E) ∈ M i ↔ (z : E × ℝ).1 ∈ W i) ∧
      (∀ z, (H z : E) ∈ (⋃ i, W i) ↔ (z : E × ℝ).2 = 0) ∧
      (∀ z, (H z : E) ∈ (⋃ i, Z i) ↔ (z : E × ℝ).2 = 1) ∧
      ∀ (i : ι) (u t : I),
        (H ⟨((G i ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E),t),
          mem_iUnion.mpr ⟨i,(hGW i _).mpr rfl⟩,t.property⟩ : E) =
          G i ⟨(u,t),u.property,t.property⟩ := by
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
  choose e _ heval using fun k : Edge => exists_affine_segment_chart
    (hpq (ri k) (rb k)) ((hr k).trans (hsegment (ri k) (rb k)))
  have hmatch (i : ι) (b : Bool) (t : I) : (G i (sidePoint b t) : E) = e (ends i b) t := by
    rw [hside,heval]
    change AffineMap.lineMap (p i b) (q i b) (t : ℝ) = AffineMap.lineMap (P (ends i b)) (Q (ends i b)) (t : ℝ)
    rw [hP,hQ]
  apply exists_global_matched_belt_product M W Z (fun k : Edge => k.1) ends G hG e hmatch
    hWsub hZsub hGW hGZ
  intro i k hik hmeet
  obtain ⟨b,c,hside,hinter⟩ := hcontact i k hik hmeet
  exact ⟨b,c,Subtype.ext hside,hinter⟩

end PoincareConjecture.M76.PrismBelt
