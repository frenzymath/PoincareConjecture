import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedCutChart
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveTerminalInterval
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabBandCoverage

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.exists_ordinary_terminal_interval
    {S s s' rim : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ rim) (hrims : rim ⊆ s) (hrimzero : rim ⊆ {x | A x = 0})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ rim → (M.chart p : E) ∈ s)
    (Ks : SimplicialComplex ℝ E) (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    {g : E → ℝ} (hg : FinitePiecewiseAffineOn g M.collar)
    (hgbound : ∀ x ∈ s ∩ {x | A x = 0}, g x ≤ 1)
    (hgR : ∀ x ∈ M.residual, g x = 0) (v : E) (hv : A.linear v = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → |t| < δ → ∀ H : E ≃ₜ E,
      (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
        FinitePiecewiseAffineOn (H : E → E) L.space) →
      (∀ x, H x = x + (t * g x) • v) →
      (∀ x ∈ s, A x ≤ A (H x)) →
      (∀ x ∈ s, A x < 0 → H x = x) →
      ∀ d : Set E, (∀ x ∈ d, A (H x) ≤ t) →
      ∀ a b : ℝ, t < a → b ≤ β →
        ∃ G : (s ∩ {x | A x ∈ Icc a b} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | A x ∈ Icc a b} : Set E),
          G.IsFinitePL ∧ ∀ x, A (G x) = A x := by
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  obtain ⟨C, hC, hCval, hCA, hCR⟩ := M.exists_selected_cut_collar_chart
    hs hs' hunion hinter hrims hrimzero hselected Ks hKs hKss
  have hcopy := hC.symm
  obtain ⟨_, ⟨KT, hKT, hKTspace, _⟩, _⟩ := hcopy
  have hgT : FinitePiecewiseAffineOn g (M.collar ∩ s) :=
    hKTspace ▸ hg.restrict KT hKT (hKTspace.subset.trans inter_subset_left)
  have hgbottom (p : {p : E × ℝ | p.1 ∈ s ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)}) (hp : (p : E × ℝ).2 = 0) :
      g (C p) = g (p : E × ℝ).1 := by
    rw [hCval, M.bottom _ hp]
  have hupper (x : E) (hx : x ∈ s ∩ {x | A x = 0}) : 0 ≤ M.upper x :=
    (M.upper_bounds x ⟨hsS hx.1, hx.2⟩).1
  obtain ⟨JR, hJR, hJRspace⟩ := M.residualComplex.exists_finite_triangulation_inter
    Ks M.residual_finite hKs
  rw [M.residual_space, hKss] at hJRspace
  obtain ⟨δ, hδ, hterminal⟩ := hC.exists_moved_collar_terminal_interval
    hupper hgbound A hCA hCR hgT hgbottom (fun x hx => hgR x hx.1)
    JR hJR hJRspace v hv
  refine ⟨δ, hδ, fun t ht htδ H hH hformula hraise hneg d hcap a b hta hb => ?_⟩
  obtain ⟨F, hF, hFA, _⟩ := hterminal t ht htδ H (hKTspace ▸ hH KT hKT)
    hformula a b hta
  have hfixR (x : E) (hx : x ∈ M.residual) : H x = x := by
    rw [hformula, hgR x hx, mul_zero, zero_smul, add_zero]
  have hsrc := cut_slab_band_eq hsS M.cover (ht.trans hta).le hb
  have htgt := (image_capped_slab_band_eq_of_cap_below hsS M.cover H hraise hneg hfixR
    (ht.trans hta) hb (fun x hx => (hcap x hx).trans_lt hta)).symm
  let G := (Homeomorph.setCongr hsrc.symm).trans (F.trans (Homeomorph.setCongr htgt))
  exact ⟨G, hF.setCongr hsrc htgt, fun x => hFA ⟨x, hsrc.symm ▸ x.property⟩⟩

end Geometry
