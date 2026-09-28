import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology
open Classical

namespace Poincare

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}

theorem exists_diffeomorph_of_local_opening
    (U V O : Opens M) (e : OpenPartialHomeomorph M M)
    (hes : e.source = (U : Set M) ∩ O) (het : e.target = (V : Set M) ∩ O)
    (he : ContMDiffOn I I ∞ e e.source)
    (hei : ContMDiffOn I I ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKO : K ⊆ O)
    (hout : ∀ x : M, x ∉ O → (x ∈ U ↔ x ∈ V))
    (hfix : ∀ x ∈ e.source, x ∉ K → e x = x)
    (hifix : ∀ x ∈ e.target, x ∉ K → e.symm x = x) :
    ∃ D : Diffeomorph I I U V ∞,
      (∀ x : U, (D x : M) = if (x : M) ∈ O then e x else x) ∧
      (∀ y : V, (D.symm y : M) = if (y : M) ∈ O then e.symm y else y) ∧
      ∀ x : U, (x : M) ∉ K → (D x : M) = x := by
  classical
  let f : M → M := fun x => if x ∈ O then e x else x
  let g : M → M := fun x => if x ∈ O then e.symm x else x
  have hfmem {x : M} (hx : x ∈ U) : f x ∈ V := by
    by_cases hxO : x ∈ O
    · have hx' : x ∈ e.source := hes.symm ▸ (show x ∈ (U : Set M) ∩ O from ⟨hx, hxO⟩)
      rw [show f x = e x from if_pos hxO]
      exact (het.subset (e.map_source hx')).1
    · simpa only [f, if_neg hxO] using (hout x hxO).mp hx
  have hgmem {y : M} (hy : y ∈ V) : g y ∈ U := by
    by_cases hyO : y ∈ O
    · have hy' : y ∈ e.target := het.symm ▸ (show y ∈ (V : Set M) ∩ O from ⟨hy, hyO⟩)
      rw [show g y = e.symm y from if_pos hyO]
      exact (hes.subset (e.map_target hy')).1
    · simpa only [g, if_neg hyO] using (hout y hyO).mpr hy
  have hfs {x : M} (hx : x ∈ U) (hxO : x ∈ O) : f x = e x := if_pos hxO
  have hgs {x : M} (hx : x ∈ V) (hxO : x ∈ O) : g x = e.symm x := if_pos hxO
  have hffix {x : M} (hx : x ∈ U) (hxK : x ∉ K) : f x = x := by
    by_cases hxO : x ∈ O
    · exact (if_pos hxO).trans (hfix x (hes.symm ▸ ⟨hx, hxO⟩) hxK)
    · exact if_neg hxO
  have hgfix {x : M} (hx : x ∈ V) (hxK : x ∉ K) : g x = x := by
    by_cases hxO : x ∈ O
    · exact (if_pos hxO).trans (hifix x (het.symm ▸ ⟨hx, hxO⟩) hxK)
    · exact if_neg hxO
  have hleft {x : M} (hx : x ∈ U) : g (f x) = x := by
    by_cases hxO : x ∈ O
    · have hxs := hes.symm ▸ (show x ∈ (U : Set M) ∩ O from ⟨hx, hxO⟩)
      have het' := het ▸ e.map_source hxs
      rw [hfs hx hxO, hgs het'.1 het'.2, e.left_inv hxs]
    · simp only [f, g, if_neg hxO]
  have hright {y : M} (hy : y ∈ V) : f (g y) = y := by
    by_cases hyO : y ∈ O
    · have hyt := het.symm ▸ (show y ∈ (V : Set M) ∩ O from ⟨hy, hyO⟩)
      have hes' := hes ▸ e.map_target hyt
      rw [hgs hy hyO, hfs hes'.1 hes'.2, e.right_inv hyt]
    · simp only [f, g, if_neg hyO]
  let F : U → V := fun x => ⟨f x, hfmem x.property⟩
  let G : V → U := fun y => ⟨g y, hgmem y.property⟩
  have hsmooth
      (A : Opens M) (j k : M → M) (hj : ContMDiffOn I I ∞ j ((A : Set M) ∩ O))
      (hkO : ∀ x ∈ A, x ∈ O → k x = j x)
      (hkK : ∀ x ∈ A, x ∉ K → k x = x) :
      ContMDiff I I ∞ (fun x : A => k x) := by
    intro x
    by_cases hxO : (x : M) ∈ O
    · have hjx : ContMDiffAt I I ∞ j (x : M) :=
        hj.contMDiffAt ((A.isOpen.inter O.isOpen).mem_nhds ⟨x.property, hxO⟩)
      have hlocal : (fun y : A => k y) =ᶠ[𝓝 x] (fun y : A => j y) := by
        filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
          (O.isOpen.mem_nhds hxO)] with y hy
        exact hkO y y.property hy
      exact (hjx.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq hlocal
    · have hxK : (x : M) ∉ K := fun h => hxO (hKO h)
      have hlocal : (fun y : A => k y) =ᶠ[𝓝 x] (fun y : A => (y : M)) := by
        filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
          (hK.isClosed.isOpen_compl.mem_nhds hxK)] with y hy
        exact hkK y y.property hy
      exact contMDiff_subtype_val.contMDiffAt.congr_of_eventuallyEq hlocal
  have hF : ContMDiff I I ∞ F := by
    apply (ContMDiff.subtypeVal_comp_iff V F).mp
    exact hsmooth U e f (hes ▸ he) (fun _ hx hxO => hfs hx hxO)
      (fun _ hx hxK => hffix hx hxK)
  have hG : ContMDiff I I ∞ G := by
    apply (ContMDiff.subtypeVal_comp_iff U G).mp
    exact hsmooth V e.symm g (het ▸ hei) (fun _ hy hyO => hgs hy hyO)
      (fun _ hy hyK => hgfix hy hyK)
  let D : Diffeomorph I I U V ∞ :=
    ⟨⟨F, G, fun x => Subtype.ext (hleft x.property),
      fun y => Subtype.ext (hright y.property)⟩, hF, hG⟩
  exact ⟨D, fun _ => rfl, fun _ => rfl, fun x hx => hffix x.property hx⟩

end Poincare
