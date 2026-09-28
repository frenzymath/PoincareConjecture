import Mathlib.Geometry.Manifold.Diffeomorph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter Classical
open scoped Manifold ContDiff Topology

namespace Poincare

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}



theorem exists_diffeomorph_of_closed_side_replacement
    (U V : Opens M) {K : Set M} (hK : IsClosed K)
    (hKU : K ⊆ U) (hKV : K ⊆ V)
    (e : OpenPartialHomeomorph M M)
    (hUs : (U : Set M) \ K ⊆ e.source)
    (hVt : (V : Set M) \ K ⊆ e.target)
    (hsU : e.source ⊆ U) (htV : e.target ⊆ V)
    (he : ContMDiffOn I I ∞ e e.source)
    (hei : ContMDiffOn I I ∞ e.symm e.target)
    (hside : ∀ x ∈ e.source, e x ∈ K ↔ x ∈ K)
    (hfix : ∀ x ∈ frontier K, e =ᶠ[𝓝 x] id)
    (hifix : ∀ x ∈ frontier K, e.symm =ᶠ[𝓝 x] id) :
    ∃ D : Diffeomorph I I U V ∞,
      (∀ x : U, (D x : M) = if (x : M) ∈ K then (x : M) else e x) ∧
      (∀ y : V, (D.symm y : M) = if (y : M) ∈ K then (y : M) else e.symm y) ∧
      ∀ x : U, (x : M) ∈ K → (D x : M) = x := by
  classical
  let f : M → M := fun x => if x ∈ K then x else e x
  let g : M → M := fun y => if y ∈ K then y else e.symm y
  have hiside (y : M) (hy : y ∈ e.target) : e.symm y ∈ K ↔ y ∈ K := by
    simpa only [e.right_inv hy] using (hside (e.symm y) (e.map_target hy)).symm
  have hfmem {x : M} (hx : x ∈ U) : f x ∈ (V : Set M) := by
    by_cases hxK : x ∈ K
    · simpa only [f, if_pos hxK] using hKV hxK
    · simpa only [f, if_neg hxK] using htV (e.map_source (hUs ⟨hx, hxK⟩))
  have hgmem {y : M} (hy : y ∈ V) : g y ∈ (U : Set M) := by
    by_cases hyK : y ∈ K
    · simpa only [g, if_pos hyK] using hKU hyK
    · simpa only [g, if_neg hyK] using hsU (e.map_target (hVt ⟨hy, hyK⟩))
  have hleft {x : M} (hx : x ∈ U) : g (f x) = x := by
    by_cases hxK : x ∈ K
    · simp only [f, g, if_pos hxK]
    · have hxs := hUs ⟨hx, hxK⟩
      have heK : e x ∉ K := fun h => hxK ((hside x hxs).mp h)
      simp only [f, g, if_neg hxK, if_neg heK, e.left_inv hxs]
  have hright {y : M} (hy : y ∈ V) : f (g y) = y := by
    by_cases hyK : y ∈ K
    · simp only [f, g, if_pos hyK]
    · have hyt := hVt ⟨hy, hyK⟩
      have hiK : e.symm y ∉ K := fun h => hyK ((hiside y hyt).mp h)
      simp only [f, g, if_neg hyK, if_neg hiK, e.right_inv hyt]
  have hsmooth (A : Opens M) (j : M → M) {O : Set M}
      (hO : IsOpen O) (hAO : (A : Set M) \ K ⊆ O)
      (hj : ContMDiffOn I I ∞ j O)
      (hjfix : ∀ x ∈ frontier K, j =ᶠ[𝓝 x] id) :
      ContMDiff I I ∞ (fun x : A => if (x : M) ∈ K then (x : M) else j x) := by
    intro x
    by_cases hxK : (x : M) ∈ K
    · apply contMDiff_subtype_val.contMDiffAt.congr_of_eventuallyEq
      by_cases hxi : (x : M) ∈ interior K
      · filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
          (isOpen_interior.mem_nhds hxi)] with y hy
        exact if_pos (interior_subset hy)
      · have hxf : (x : M) ∈ frontier K := hK.frontier_eq.symm ▸ ⟨hxK, hxi⟩
        filter_upwards [continuous_subtype_val.continuousAt.eventually (hjfix x hxf)] with y hy
        by_cases hyK : (y : M) ∈ K
        · exact if_pos hyK
        · exact (if_neg hyK).trans hy
    · have hjx := hj.contMDiffAt (hO.mem_nhds (hAO ⟨x.property, hxK⟩))
      apply (hjx.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
        (hK.isOpen_compl.mem_nhds hxK)] with y hy
      exact if_neg hy
  let F : U → V := fun x => ⟨f x, hfmem x.property⟩
  let G : V → U := fun y => ⟨g y, hgmem y.property⟩
  have hF : ContMDiff I I ∞ F := by
    apply (ContMDiff.subtypeVal_comp_iff V F).mp
    exact hsmooth U e e.open_source hUs he hfix
  have hG : ContMDiff I I ∞ G := by
    apply (ContMDiff.subtypeVal_comp_iff U G).mp
    exact hsmooth V e.symm e.open_target hVt hei hifix
  let D : Diffeomorph I I U V ∞ :=
    ⟨⟨F, G, fun x => Subtype.ext (hleft x.property),
      fun y => Subtype.ext (hright y.property)⟩, hF, hG⟩
  exact ⟨D, fun _ => rfl, fun _ => rfl, fun _ hx => if_pos hx⟩

end Poincare
