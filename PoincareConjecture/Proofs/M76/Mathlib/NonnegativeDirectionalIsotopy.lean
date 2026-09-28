import PoincareConjecture.Proofs.M76.Mathlib.NonnegativeRelativePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.SmallSupportedPLIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLTransport









set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem FinitePiecewiseAffineOn.exists_nonnegative_directional_isotopy_with_global_finitePL
    {f : E → ℝ} {S U T : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hnonneg : ∀ x ∈ S, 0 ≤ f x) (v : E)
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
          S ∪ Q.space ∪ T ⊆ interior K.space ∧
          FinitePiecewiseAffineOn g K.space ∧
          (∀ x, x ∉ K.space → g x = 0) ∧
          (∀ t : Icc (-ε) ε, FinitePiecewiseAffineOn (H t : E → E) K.space) ∧
          ∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
            FinitePiecewiseAffineOn (H t : E → E) L.space := by
  classical
  have hcompact := (hf.isCompact.union (Q.isCompact_space_of_finite hQ)).union hT
  obtain ⟨K, hK, hcv, hRK⟩ :=
    hcompact.exists_finite_convex_neighborhood
  obtain ⟨g, hg, hgf, hgn, hgQ, hgU, hgK⟩ :=
    hf.exists_nonnegative_relative_extension hnonneg Q hQ hzeroQ K hK
      ((subset_union_left.trans hRK).trans interior_subset)
      (hU.inter isOpen_interior) (subset_inter hSU
        (subset_union_left.trans (subset_union_left.trans hRK)))
  let a : ℝ →ᴬ[ℝ] E := ((ContinuousLinearMap.id ℝ ℝ).smulRight v).toContinuousAffineMap
  have hgv : FinitePiecewiseAffineOn (fun x => g x • v) K.space := hg.postcomp a
  have hfront : ∀ x ∈ frontier K.space, g x • v = 0 := by
    intro x hx
    rw [hgU x (fun hi => hx.2 hi.2), zero_smul]
  obtain ⟨ε, hε, H, hc, hci, hformula, hrest⟩ := hgv.exists_small_supported_isotopy hcv hfront
  have hfullformula (t : Icc (-ε) ε) (x : E) :
      H t x = x + ((t : ℝ) * g x) • v := by
    rw [hformula]
    by_cases hx : x ∈ K.space
    · rw [indicator_of_mem hx, smul_smul]
    · rw [indicator_of_notMem hx, hgK x hx, mul_zero, zero_smul, smul_zero]
  have hPL (t : Icc (-ε) ε) : FinitePiecewiseAffineOn (H t : E → E) K.space := by
    obtain ⟨_, _, e, he, heval⟩ := hrest t
    obtain ⟨F, hF, hFe⟩ := he
    exact hF.congr (fun x hx => (hFe ⟨x, hx⟩).symm.trans (heval ⟨x, hx⟩))
  refine ⟨g, hgn, hgf, hgQ, fun x hx => hgU x (fun hi => hx hi.1),
    ε, hε, H, hc, hci, hfullformula, K, hK, hcv, hRK, hg, hgK, hPL, ?_⟩
  intro t L hL
  apply (hPL t).homeomorph_on_finite_polyhedron_of_eq_id_off (L := L) (hL := hL)
  intro x hx
  rw [hfullformula, hgK x hx, mul_zero, zero_smul, add_zero]





theorem FinitePiecewiseAffineOn.exists_nonnegative_directional_isotopy
    {f : E → ℝ} {S U T : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hnonneg : ∀ x ∈ S, 0 ≤ f x) (v : E)
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
          S ∪ Q.space ∪ T ⊆ interior K.space ∧
          ∀ t : Icc (-ε) ε, FinitePiecewiseAffineOn (H t : E → E) K.space := by
  obtain ⟨g, hgn, hgf, hgQ, hgU, ε, hε, H, hc, hci, hformula,
      K, hK, hcv, hcover, _, _, hPL, _⟩ :=
    hf.exists_nonnegative_directional_isotopy_with_global_finitePL
      hnonneg v Q hQ hzeroQ hU hSU hT
  exact ⟨g, hgn, hgf, hgQ, hgU, ε, hε, H, hc, hci, hformula,
    K, hK, hcv, hcover, hPL⟩

end Geometry
