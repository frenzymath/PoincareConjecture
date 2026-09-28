import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedEndComposition










set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞




theorem diffeomorph_image_eq_self_of_tsupport_disjoint
    (F : D3) (K X : Set E3)
    (hforward : tsupport (fun y : E3 => F y - y) ⊆ K)
    (hinverse : tsupport (fun y : E3 => F.symm y - y) ⊆ K)
    (hdis : Disjoint K X) :
    F '' X = X ∧ F.symm '' X = X := by
  have hfix (y : E3) (hy : y ∈ X) : F y = y := by
    apply sub_eq_zero.mp
    exact image_eq_zero_of_notMem_tsupport (f := fun y : E3 => F y - y) (by
      intro hyK
      exact Set.disjoint_left.mp hdis (hforward hyK) hy)
  have hfixi (y : E3) (hy : y ∈ X) : F.symm y = y := by
    apply sub_eq_zero.mp
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y : E3 => F.symm y - y) (by
        intro hyK
        exact Set.disjoint_left.mp hdis (hinverse hyK) hy)
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hfix x hx] using hx
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hfixi x hx] using hx
    · intro hy
      exact ⟨y, hy, hfixi y hy⟩






theorem exists_nonnested_end_exchange_compatibility
    (g h : D3) (S R E₀ E₁ P S₀ S₁ Q : Set E3)
    (hS : S = R ∪ E₀ ∪ E₁ ∪ P)
    (hgR : g '' R = R) (hg0 : g '' E₀ = S₀)
    (hg1 : g '' E₁ = S₁) (hgP : g '' P = P)
    (hhR : h '' R = R) (hh0 : h '' S₀ = S₀)
    (hh1 : h '' S₁ = S₁) (hhP : h '' P = Q)
    (hgiR : g.symm '' R = R) (hgi0 : g.symm '' S₀ = E₀)
    (hgi1 : g.symm '' S₁ = E₁) (hgiP : g.symm '' P = P)
    (hhiR : h.symm '' R = R) (hhi0 : h.symm '' S₀ = S₀)
    (hhi1 : h.symm '' S₁ = S₁) (hhiP : h.symm '' Q = P) :
    ∃ K : D3,
      K = g.trans h ∧
      K '' S = R ∪ S₀ ∪ S₁ ∪ Q ∧
      K.symm '' (R ∪ S₀ ∪ S₁ ∪ Q) = S := by
  let K : D3 := g.trans h
  have hforward : K '' S = R ∪ S₀ ∪ S₁ ∪ Q := by
    calc
      K '' S = h '' (g '' S) := by
        change (g.trans h) '' S = _
        rw [Diffeomorph.coe_trans, Set.image_comp]
      _ = h '' (g '' (R ∪ E₀ ∪ E₁ ∪ P)) := by rw [hS]
      _ = h '' (g '' R ∪ g '' E₀ ∪ g '' E₁ ∪ g '' P) := by
        simp only [image_union]
      _ = h '' (R ∪ S₀ ∪ S₁ ∪ P) := by rw [hgR, hg0, hg1, hgP]
      _ = h '' R ∪ h '' S₀ ∪ h '' S₁ ∪ h '' P := by
        rw [image_union, image_union, image_union]
      _ = R ∪ S₀ ∪ S₁ ∪ Q := by rw [hhR, hh0, hh1, hhP]
  have hinverse : K.symm '' (R ∪ S₀ ∪ S₁ ∪ Q) = S := by
    calc
      K.symm '' (R ∪ S₀ ∪ S₁ ∪ Q) =
          g.symm '' (h.symm '' (R ∪ S₀ ∪ S₁ ∪ Q)) := by
        change (g.trans h).symm '' _ = _
        rw [Diffeomorph.symm_trans', Diffeomorph.coe_trans, Set.image_comp]
      _ = g.symm '' (h.symm '' R ∪ h.symm '' S₀ ∪ h.symm '' S₁ ∪ h.symm '' Q) := by
        simp only [image_union]
      _ = g.symm '' (R ∪ S₀ ∪ S₁ ∪ P) := by rw [hhiR, hhi0, hhi1, hhiP]
      _ = g.symm '' R ∪ g.symm '' S₀ ∪ g.symm '' S₁ ∪ g.symm '' P := by
        rw [image_union, image_union, image_union]
      _ = R ∪ E₀ ∪ E₁ ∪ P := by rw [hgiR, hgi0, hgi1, hgiP]
      _ = S := hS.symm
  exact ⟨K, rfl, hforward, hinverse⟩

end PoincareConjecture.M25.Topology3D
