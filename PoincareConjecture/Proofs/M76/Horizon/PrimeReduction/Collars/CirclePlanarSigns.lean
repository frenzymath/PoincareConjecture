import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleTube
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem exists_coordinate_identity_circle_tube
    (P : Fin 3 → SimplicialComplex ℝ V3) (hP : ∀ i, (P i).faces.Finite)
    {m : ℕ} (L : Polygon V3 (m + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) (hPL : (P 2).space = L.boundary ℝ)
    {W : Set V3} (hW : IsOpen W) (hLW : L.boundary ℝ ⊆ W)
    (hisolate : ∀ x ∈ W, x ∈ L.boundary ℝ ↔ x ∈ (P 0).space ∧ x ∈ (P 1).space)
    (hcharts : ∀ x ∈ L.boundary ℝ, ∃ B : OpenPartialHomeomorph V3 V3,
      x ∈ B.source ∧ B ∈ piecewiseAffineGroupoid V3 ∧
      ∀ (i : Fin 2) y, y ∈ B.source → (y ∈ (P i.castSucc).space ↔ B y i.castSucc = 0))
    (f : Fin 2 → V3 → V2)
    (hf : ∀ i, FinitePiecewiseAffineOn (f i) (P i.castSucc).space)
    (hfi : ∀ i, InjOn (f i) (P i.castSucc).space) :
    ∃ (n : ℕ) (sigma : C3 → V3),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) W ∧
      L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) ∧
      (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))),
        sigma x ∈ (P k.castSucc).space ↔ (x : C3).1 ∈ signedTubeSheet k) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x ∈ L.boundary ℝ ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ ↦ sigma ((0, 0), t)) '' Icc (0 : ℝ) (n + 3) = L.boundary ℝ ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x = sigma y ↔ (x : C3).1 = (y : C3).1 ∧
          ((x : C3).2 = (y : C3).2 ∨
            ((x : C3).2 = 0 ∧ (y : C3).2 = n + 3) ∨
            ((y : C3).2 = 0 ∧ (x : C3).2 = n + 3)) := by
  classical
  obtain ⟨n, closing, sigma, hSigma, hSW, hInt, hSheets, hAxis, hAxisImage, hFib⟩ :=
    exists_coordinate_signed_circle_tube P hP L hL hLi hPL hW hLW hisolate hcharts
  have hLP (j : Fin 2) : L.boundary ℝ ⊆ (P j.castSucc).space := by
    intro x hx
    have h := (hisolate x (hLW hx)).mp hx
    fin_cases j
    · exact h.1
    · exact h.2
  have hpolygons (j : Fin 2) : ∃ k : ℕ, ∃ Q : Polygon V2 (k + 3),
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧ Q.boundary ℝ = f j '' L.boundary ℝ :=
    L.exists_polygon_finitePL_image hL hLi (hf j) (hLP j) ((hfi j).mono (hLP j))
  choose k Q hQi hQ hQb using hpolygons
  choose u hu huf using fun j => (hf j).exists_homeomorph_image (hfi j)
  have huaxis (j : Fin 2) (z : (P j.castSucc).space) :
      (u j z : V2) ∈ (Q j).boundary ℝ ↔ (z : V3) ∈ L.boundary ℝ := by
    rw [huf, hQb]
    constructor
    · rintro ⟨x, hx, heq⟩
      exact (hfi j) (hLP j hx) z.property heq ▸ hx
    · exact fun hz => mem_image_of_mem (f j) hz
  have hclosing := signed_diamond_closing_eq_true
    (by positivity : (0 : ℝ) < n + 3) sigma closing hSigma hFib
    (fun j => (P j.castSucc).space) (fun j => f j '' (P j.castSucc).space)
    (L.boundary ℝ) u hu k Q hQ hQi hSheets hAxis huaxis
  have hcloseEq : closing = fun _ => true := funext hclosing
  refine ⟨n, sigma, hSigma, hSW, hInt, hSheets, hAxis, hAxisImage, ?_⟩
  intro x y
  rw [hFib, hcloseEq]
  simp only [signedTubeReflection_apply, ↓reduceIte, one_mul, Prod.eta]
  constructor
  · rintro (h | h | h)
    · cases h
      exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨h.2.2, Or.inr (Or.inl ⟨h.1, h.2.1⟩)⟩
    · exact ⟨h.2.2.symm, Or.inr (Or.inr ⟨h.1, h.2.1⟩)⟩
  · rintro ⟨hxy, h | h | h⟩
    · exact Or.inl (Subtype.ext (Prod.ext hxy h))
    · exact Or.inr (Or.inl ⟨h.1, h.2, hxy⟩)
    · exact Or.inr (Or.inr ⟨h.1, h.2, hxy.symm⟩)

end PoincareConjecture.M76
