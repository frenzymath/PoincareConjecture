import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Push
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H A M : Type*} [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}

theorem exists_boundary_graph_push
    (U : Opens M)
    (e : Diffeomorph I 𝓘(Real, E × Real) U (E × Real) ∞)
    (b : E -> Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b)
    {D : Set M}
    (hD : D ∩ U = (fun p : E × Real => (e.symm p : M)) '' {p | p.2 ≤ 0}) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
      ∃ F : Diffeomorph I I M M ∞,
        (∀ x ∉ K, F x = x) ∧
        (∀ x : E, F (e.symm (x, 0) : M) = (e.symm (x, b x) : M)) ∧
        F '' D = (D \ U) ∪
          (fun p : E × Real => (e.symm p : M)) '' {p | p.2 ≤ b p.1} := by
  obtain ⟨R, _, G, _, hGfix, hGzero, hGside⟩ := exists_supported_graph_push b hb hbc
  let K₀ : Set (E × Real) := tsupport b ×ˢ Metric.closedBall 0 R
  have hK₀ : IsCompact K₀ := hbc.prod (isCompact_closedBall 0 R)
  let K : Set M := (fun p : E × Real => (e.symm p : M)) '' K₀
  have hK : IsCompact K := hK₀.image (continuous_subtype_val.comp e.symm.continuous)
  have hKU : K ⊆ U := by
    rintro x ⟨p, _, rfl⟩
    exact (e.symm p).property
  let g : Diffeomorph I I U U ∞ := (e.trans G).trans e.symm
  have hgfix (x : U) (hx : (x : M) ∉ K) : g x = x := by
    have hnot : e x ∉ K₀ := by
      intro hp
      exact hx ⟨e x, hp, by simp⟩
    change e.symm (G (e x)) = x
    rw [hGfix _ hnot, e.symm_apply_apply]
  obtain ⟨F, hF, hFfix⟩ := Diffeomorph.exists_extension_of_isCompact U g hK hKU hgfix
  have hcoord (p : E × Real) :
      F (e.symm p : M) = (e.symm (G p) : M) := by
    rw [hF]
    change (e.symm (G (e (e.symm p))) : M) = (e.symm (G p) : M)
    rw [e.apply_symm_apply]
  refine ⟨K, hK, hKU, F, hFfix, ?_, ?_⟩
  · intro x
    rw [hcoord, hGzero]
  · have hdecomp : D = (D \ U) ∪
        (fun p : E × Real => (e.symm p : M)) '' {p | p.2 ≤ 0} := by
      rw [← hD]
      exact (sdiff_union_inter D (U : Set M)).symm
    have hout : F '' (D \ U) = D \ U := by
      calc
        F '' (D \ U) = id '' (D \ U) := by
          apply image_congr
          intro x hx
          exact hFfix x (fun h => hx.2 (hKU h))
        _ = D \ U := image_id _
    conv_lhs => rw [hdecomp, image_union, hout]
    congr 1
    calc
      F '' ((fun p : E × Real => (e.symm p : M)) '' {p | p.2 ≤ 0}) =
          (fun p : E × Real => (e.symm p : M)) ''
            (G '' {p | p.2 ≤ 0}) := by
        simp only [image_image]
        apply image_congr
        intro p _
        exact hcoord p
      _ = _ := by rw [hGside]

end Poincare.Manifold.Schoenflies
