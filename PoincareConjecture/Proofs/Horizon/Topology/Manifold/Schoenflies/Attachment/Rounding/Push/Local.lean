import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Graph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport

set_option autoImplicit false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

private theorem image_eq_patch {X : Type*} (F : X ≃ X) {D S O : Set X}
    (hfix : ∀ x ∉ O, F x = x) (hDS : D ∩ O = S ∩ O) :
    F '' D = (D \ O) ∪ ((F '' S) ∩ O) := by
  have hmem (x : X) : F x ∈ O ↔ x ∈ O := by
    constructor
    · intro hx
      by_contra hn
      exact hn (hfix x hn ▸ hx)
    · intro hx
      by_contra hn
      have he : x = F x := F.injective (hfix (F x) hn).symm
      exact hn (he ▸ hx)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hxo : x ∈ O
    · right
      have hxs : x ∈ S := (show x ∈ S ∩ O from hDS ▸ ⟨hx, hxo⟩).1
      exact ⟨⟨x, hxs, rfl⟩, (hmem x).2 hxo⟩
    · left
      rw [hfix x hxo]
      exact ⟨hx, hxo⟩
  · rintro (⟨hy, hyo⟩ | ⟨⟨x, hx, rfl⟩, hyo⟩)
    · exact ⟨y, hy, hfix y hyo⟩
    · have hxo := (hmem x).1 hyo
      exact ⟨x, (show x ∈ D ∩ O from hDS.symm ▸ ⟨hx, hxo⟩).1, rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H A M : Type*} [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}

theorem exists_boundary_graph_push_within
    (C : Opens M) (e : Diffeomorph I 𝓘(Real, E × Real) C (E × Real) ∞)
    (b : E → Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b)
    {O : Set M} (hO : IsOpen O) (hOC : O ⊆ C)
    (htrace : ∀ x ∈ tsupport b, ∀ t ∈ Icc (0 : Real) 1,
      (e.symm (x, t * b x) : M) ∈ O) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ O ∧
      ∃ F : Diffeomorph I I M M ∞,
        (∀ x ∉ K, F x = x) ∧
        (∀ x, F (e.symm (x, 0) : M) = (e.symm (x, b x) : M)) ∧
        (∀ D : Set M,
          D ∩ O = ((fun p : E × Real => (e.symm p : M)) '' {p | p.2 ≤ 0}) ∩ O →
          F '' D = (D \ O) ∪
            (((fun p : E × Real => (e.symm p : M)) '' {p | p.2 ≤ b p.1}) ∩ O)) ∧
        (∀ D : Set M,
          D ∩ O = ((fun p : E × Real => (e.symm p : M)) '' {p | 0 ≤ p.2}) ∩ O →
          F '' D = (D \ O) ∪
            (((fun p : E × Real => (e.symm p : M)) '' {p | b p.1 ≤ p.2}) ∩ O)) := by
  let q : E × Real → M := fun p => (e.symm p : M)
  have hq : Continuous q := continuous_subtype_val.comp e.symm.continuous
  obtain ⟨K₀, hK₀, hK₀O, G, hGfirst, hGfix, hGzero, hGlower⟩ :=
    exists_graph_push_within b hb hbc (hO.preimage hq) htrace
  let K := q '' K₀
  have hK : IsCompact K := hK₀.image hq
  have hKO : K ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact hK₀O hp
  have hKC : K ⊆ C := hKO.trans hOC
  let g : Diffeomorph I I C C ∞ := (e.trans G).trans e.symm
  have hgfix (x : C) (hx : (x : M) ∉ K) : g x = x := by
    have hnot : e x ∉ K₀ := by
      intro hp
      apply hx
      exact ⟨e x, hp, by simp [q]⟩
    change e.symm (G (e x)) = x
    rw [hGfix _ hnot, e.symm_apply_apply]
  obtain ⟨F, hF, hFfix⟩ :=
    Diffeomorph.exists_extension_of_isCompact C g hK hKC hgfix
  have hcoord (p : E × Real) : F (q p) = q (G p) := by
    rw [hF]
    change (e.symm (G (e (e.symm p))) : M) = (e.symm (G p) : M)
    rw [e.apply_symm_apply]
  have himage (S : Set (E × Real)) : F '' (q '' S) = q '' (G '' S) := by
    simp only [image_image]
    exact image_congr fun p _ => hcoord p
  refine ⟨K, hK, hKO, F, hFfix, ?_, ?_, ?_⟩
  · intro x
    change F (q (x, 0)) = q (x, b x)
    rw [hcoord, hGzero]
  · intro D hD
    change F '' D = (D \ O) ∪ ((q '' {p | p.2 ≤ b p.1}) ∩ O)
    have hpatch : F '' D = (D \ O) ∪ ((F '' (q '' {p | p.2 ≤ 0})) ∩ O) :=
      image_eq_patch F.toEquiv (fun x hx => hFfix x (fun h => hx (hKO h))) hD
    rw [hpatch, himage, hGlower]
  · intro D hD
    change F '' D = (D \ O) ∪ ((q '' {p | b p.1 ≤ p.2}) ∩ O)
    have hpatch : F '' D = (D \ O) ∪ ((F '' (q '' {p | 0 ≤ p.2})) ∩ O) :=
      image_eq_patch F.toEquiv (fun x hx => hFfix x (fun h => hx (hKO h))) hD
    have hupper : G '' {p | 0 ≤ p.2} = {p | b p.1 ≤ p.2} :=
      image_upperHalfSpace_eq_supergraph G.toHomeomorph hGfirst hK₀ hGfix b hGzero
    rw [hpatch, himage, hupper]

end Poincare.Manifold.Schoenflies.Rounding
