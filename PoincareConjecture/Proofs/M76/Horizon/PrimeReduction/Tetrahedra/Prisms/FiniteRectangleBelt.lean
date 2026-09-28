import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MatchedRectangleBelt

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PrismBelt

local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_finite_rectangular_belt_product
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (M W Z : ι → Set E) (L : κ → Set E) (ends : ι → Bool → κ) (p q : κ → E)
    (hL : ∀ k, IsFinitePLBallPair ℝ (L k) {p k, q k}) (hpq : ∀ k, p k ≠ q k)
    (hM : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (M i)
      ((W i ∪ Z i) ∪ (L (ends i false) ∪ L (ends i true))))
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {p (ends i false), p (ends i true)})
    (hZ : ∀ i, IsFinitePLBallPair ℝ (Z i) {q (ends i false), q (ends i true)})
    (hWZ : ∀ i, Disjoint (W i) (Z i))
    (hLR : ∀ i, Disjoint (L (ends i false)) (L (ends i true)))
    (hWL : ∀ i b, W i ∩ L (ends i b) = {p (ends i b)})
    (hZL : ∀ i b, Z i ∩ L (ends i b) = {q (ends i b)})
    (hcontact : ∀ i j, i ≠ j → (M i ∩ M j).Nonempty →
      ∃ b c, ends i b = ends j c ∧ M i ∩ M j = L (ends i b)) :
    ∃ H : ((⋃ i, W i) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i), H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ ⋃ i, W i),
        (H ⟨(x, 0), hx, le_rfl, zero_le_one⟩ : E) = x) ∧
      (∀ i x, (H x : E) ∈ M i ↔ (x : E × ℝ).1 ∈ W i) ∧
      (∀ x, (H x : E) ∈ (⋃ i, W i) ↔ (x : E × ℝ).2 = 0) ∧
      (∀ x, (H x : E) ∈ (⋃ i, Z i) ↔ (x : E × ℝ).2 = 1) := by
  classical
  choose e he he0 he1 using fun k => (hL k).exists_unitInterval_chart_with_endpoints (hpq k)
  have hp (i : ι) : p (ends i false) ≠ p (ends i true) := by
    intro h
    exact disjoint_left.mp (hLR i)
      ((hL (ends i false)).1 (show p (ends i false) ∈ {p (ends i false), q (ends i false)} by simp))
      (h.symm ▸ (hL (ends i true)).1 (show p (ends i true) ∈ {p (ends i true), q (ends i true)} by simp))
  have hq (i : ι) : q (ends i false) ≠ q (ends i true) := by
    intro h
    exact disjoint_left.mp (hLR i)
      ((hL (ends i false)).1 (show q (ends i false) ∈ {p (ends i false), q (ends i false)} by simp))
      (h.symm ▸ (hL (ends i true)).1 (show q (ends i true) ∈ {p (ends i true), q (ends i true)} by simp))
  have hex (i : ι) := exists_rectangle_with_prescribed_vertical_sides
    (hM i) (hW i) (hZ i) (hp i) (hq i) (e (ends i false)) (e (ends i true))
    (he _) (he _) (he0 _) (he1 _) (he0 _) (he1 _)
    (hWZ i) (hLR i) (hWL i false) (hWL i true) (hZL i false) (hZL i true)
  choose G hG hGl hGr hGW hGZ _ _ using hex
  have hside (i : ι) (b : Bool) (t : I) :
      (G i (sidePoint b t) : E) = e (ends i b) t := by
    cases b
    · exact hGl i t
    · exact hGr i t
  exact exists_matched_rectangle_belt_product M W Z L ends G hG e hside
    (fun i x hx => (hM i).1 (Or.inl (Or.inl hx)))
    (fun i x hx => (hM i).1 (Or.inl (Or.inr hx))) hGW hGZ hcontact

end PoincareConjecture.M76.PrismBelt
