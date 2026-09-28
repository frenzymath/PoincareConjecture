import PoincareConjecture.Proofs.M76.Mathlib.NonnegativeDirectionalIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLAffineScalarDisplacement

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.exists_certified_directional_isotopy_with_global_finitePL
    {f : E → ℝ} {S U T : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hnonneg : ∀ x ∈ S, 0 ≤ f x) (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hzeroQ : ∀ x ∈ S ∩ Q.space, f x = 0)
    (hU : IsOpen U) (hSU : S ⊆ U) (hT : IsCompact T) :
    ∃ g : E → ℝ, (∀ x, 0 ≤ g x) ∧ EqOn g f S ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
          S ∪ Q.space ∪ T ⊆ interior K.space ∧ FinitePiecewiseAffineOn g K.space ∧
          (∀ x, x ∉ K.space → g x = 0) ∧
          (∀ t : Icc (-ε) ε, FinitePiecewiseAffineOn (H t : E → E) K.space) ∧
          ∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
            FinitePiecewiseAffineOn (H t : E → E) L.space := by
  obtain ⟨g, hgn, hgf, hgQ, hgU, ε, hε, H, hc, hci, hformula,
      K, hK, hcv, hcover, _, hgK, hPL, hglobal⟩ :=
    hf.exists_nonnegative_directional_isotopy_with_global_finitePL
      hnonneg v Q hQ hzeroQ hU hSU hT
  let t : Icc (-ε) ε := ⟨ε, neg_le_self hε.le, le_rfl⟩
  let Ac : E →ᴬ[ℝ] ℝ := ⟨A, A.continuous_of_finiteDimensional⟩
  have hg : FinitePiecewiseAffineOn g K.space :=
    (hPL t).scalar_of_affine_displacement Ac Ac hε.ne' (fun x _ => by
      change A (H t x) = A x + ε * g x
      rw [hformula, add_comm x]
      change A ((ε * g x) • v +ᵥ x) = A x + ε * g x
      rw [A.map_vadd, map_smul, hv]
      change ε * g x * 1 + A x = A x + ε * g x
      ring)
  exact ⟨g, hgn, hgf, hgQ, hgU, ε, hε, H, hc, hci, hformula,
    K, hK, hcv, hcover, hg, hgK, hPL, hglobal⟩

theorem FinitePiecewiseAffineOn.exists_certified_directional_isotopy
    {f : E → ℝ} {S U T : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hnonneg : ∀ x ∈ S, 0 ≤ f x) (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hzeroQ : ∀ x ∈ S ∩ Q.space, f x = 0)
    (hU : IsOpen U) (hSU : S ⊆ U) (hT : IsCompact T) :
    ∃ g : E → ℝ, (∀ x, 0 ≤ g x) ∧ EqOn g f S ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
          S ∪ Q.space ∪ T ⊆ interior K.space ∧ FinitePiecewiseAffineOn g K.space ∧
          ∀ t : Icc (-ε) ε, FinitePiecewiseAffineOn (H t : E → E) K.space := by
  obtain ⟨g, hgn, hgf, hgQ, hgU, ε, hε, H, hc, hci, hformula,
      K, hK, hcv, hcover, hg, _, hPL, _⟩ :=
    hf.exists_certified_directional_isotopy_with_global_finitePL
      hnonneg A v hv Q hQ hzeroQ hU hSU hT
  exact ⟨g, hgn, hgf, hgQ, hgU, ε, hε, H, hc, hci, hformula,
    K, hK, hcv, hcover, hg, hPL⟩

end Geometry
