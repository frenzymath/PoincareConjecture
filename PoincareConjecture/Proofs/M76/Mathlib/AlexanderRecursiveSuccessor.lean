import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedCover
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem AlexanderCollarSlab.nonempty_selected_successor
    {S s d TX TY X : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) (hs : s ⊆ S)
    (hsplit : M.collar ∩ s = TX ∪ TY) (hd : d ⊆ {x | A x = 0})
    (hcontact : TX ∩ ((M.residual ∩ s) ∪ (TY ∪ d)) = TX ∩ M.residual)
    (hTYzero : TY ∩ {x | A x = 0} ⊆ d)
    (H : E ≃ₜ E) (hraise : ∀ x, A x ≤ A (H x))
    (hneg : ∀ x ∈ s, A x < 0 → H x = x)
    (hhigh : ∀ x, β ≤ A x → H x = x)
    (hR : ∀ x ∈ M.residual, H x = x)
    (hcapzero : (H '' d) ∩ {x | A x = 0} ⊆ {q})
    (hglobal : ∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) L.space)
    (hzero : (H '' (s ∪ d)) ∩ {x | A x = 0} = X)
    (hX : X ⊆ S ∩ {x | A x = 0}) (hqX : q ∈ X)
    (Ks Kd KY KX : SimplicialComplex ℝ E)
    (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    (hKd : Kd.faces.Finite) (hKds : Kd.space = d)
    (hKY : KY.faces.Finite) (hKYs : KY.space = TY)
    (hKX : KX.faces.Finite) (hKXs : KX.space = X)
    (D : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)} ≃ₜ (H '' TX))
    (hD : D.IsFinitePL) (hDheight : ∀ p, A (D p) = (p : E × ℝ).2)
    (hDbottom : ∀ p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).2 = 0 → (D p : E) = (p : E × ℝ).1)
    (hDcontact : ∀ p, (D p : E) ∈ H '' M.residual ↔
      (p : E × ℝ).2 = M.upper (p : E × ℝ).1) :
    Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) := by
  have hTY : TY ⊆ M.collar :=
    (subset_union_right.trans hsplit.symm.subset).trans inter_subset_left
  obtain ⟨J₀, hJ₀, hJ₀s⟩ := M.residualComplex.exists_finite_triangulation_inter Ks
    M.residual_finite hKs
  rw [M.residual_space, hKss] at hJ₀s
  obtain ⟨W, hW, hWs⟩ := KY.exists_finite_triangulation_union Kd hKY hKd
  rw [hKYs, hKds] at hWs
  have hHW : FinitePiecewiseAffineOn (H : E → E) (TY ∪ d) := hWs ▸ hglobal W hW
  obtain ⟨e, he, _⟩ := hHW.exists_homeomorph_image H.injective.injOn
  have hcopy := he.symm
  obtain ⟨_, ⟨J₁, hJ₁, hJ₁s, _⟩, _⟩ := hcopy
  obtain ⟨J, hJ, hJs⟩ := J₀.exists_finite_triangulation_union J₁ hJ₀ hJ₁
  rw [hJ₀s, hJ₁s] at hJs
  let Rnew := (M.residual ∩ s) ∪ (H '' (TY ∪ d))
  have hfixRcut : H '' (M.residual ∩ s) = M.residual ∩ s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hR y hy.1).symm ▸ hy
    · exact fun hx => ⟨x, hx, hR x hx.1⟩
  have hRimage : H '' ((M.residual ∩ s) ∪ (TY ∪ d)) = Rnew := by
    rw [image_union, hfixRcut]
  have hnewContact : (H '' TX) ∩ Rnew = (H '' TX) ∩ (H '' M.residual) := by
    rw [← hRimage, ← image_inter H.injective, hcontact, image_inter H.injective]
  have hupperX : FinitePiecewiseAffineOn M.upper X :=
    hKXs ▸ M.upper_finitePL.restrict KX hKX (hKXs.subset.trans hX)
  have hdomain : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)} =
      {p : E × ℝ | p.1 ∈ (H '' (s ∪ d)) ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)} := by rw [hzero]
  let C := (Homeomorph.setCongr hdomain.symm).trans
    (D.trans (Homeomorph.setCongr rfl))
  refine ⟨{
    width_pos := M.width_pos
    apex_mem := (hzero.symm.subset hqX).1
    apex_height := M.apex_height
    upper := M.upper
    collar := H '' TX
    residual := Rnew
    residualComplex := J
    chart := C
    chart_finitePL := hD.setCongr hdomain rfl
    residual_finite := hJ
    residual_space := hJs
    cover := M.selected_image_closed_slab_eq hs hsplit hd H hraise hneg hhigh hR
    residual_zero := M.selected_residual_zero_subset hTY hTYzero H hraise hcapzero
    roof_contact := ?_
    upper_finitePL := hzero.symm ▸ hupperX
    upper_bounds := fun x hx => M.upper_bounds x (hX (hzero.subset hx))
    apex_upper := M.apex_upper
    upper_pos := fun x hx => M.upper_pos x (hX (hzero.subset hx))
    height := fun p => hDheight ⟨p, hdomain.symm ▸ p.property⟩
    bottom := fun p => hDbottom ⟨p, hdomain.symm ▸ p.property⟩
    bottom_covered := ?_ }⟩
  · intro p
    have htest : (C p : E) ∈ Rnew ↔ (C p : E) ∈ H '' M.residual :=
      ⟨fun hp => (hnewContact.subset ⟨(C p).property, hp⟩).2,
        fun hp => (hnewContact.symm.subset ⟨(C p).property, hp⟩).2⟩
    exact htest.trans (hDcontact ⟨p, hdomain.symm ▸ p.property⟩)
  · intro x hx
    let p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)} :=
      ⟨(x, 0), hzero.subset hx, le_rfl, (M.upper_bounds x (hX (hzero.subset hx))).1⟩
    have hp : (D p : E) = x := hDbottom p rfl
    have hmem : (D p : E) ∈ H '' TX := (D p).property
    rw [hp] at hmem
    exact hmem

end Geometry
