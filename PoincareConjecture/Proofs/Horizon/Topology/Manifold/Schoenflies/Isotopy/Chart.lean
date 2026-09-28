import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E A H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}



theorem exists_supported_chart_isotopy
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn 𝓘(Real, E) I ∞ e e.source)
    (hei : ContMDiffOn I 𝓘(Real, E) ∞ e.symm e.target)
    {L : Set E} (hL : IsCompact L) (hLs : L ⊆ e.source)
    (F : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hF0 : ∀ x, F 0 x = x)
    (hFs : ContDiff Real ∞ (fun p : Real × E => F p.1 p.2))
    (hFfix : ∀ t x, x ∉ L -> F t x = x) :
    IsCompact (e '' L) ∧ e '' L ⊆ e.target ∧
      ∃ Phi : Real -> Diffeomorph I I M M ∞,
      (∀ x, Phi 0 x = x) ∧
      ContMDiff (𝓘(Real, Real).prod I) I ∞ (fun p : Real × M => Phi p.1 p.2) ∧
      (∀ t x, x ∉ e '' L -> Phi t x = x) ∧
      ∀ t x, x ∈ e.source -> Phi t (e x) = e (F t x) := by
  classical
  have hfixsymm (t : Real) (x : E) (hx : x ∉ L) :
      (F t).symm x = x := by
    apply (F t).injective
    change F t ((F t).symm x) = F t x
    rw [(F t).apply_symm_apply, hFfix t x hx]
  have hmaps (D : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
      (hD : ∀ x ∉ L, D x = x) : MapsTo D e.source e.source := by
    intro x hx
    by_contra hout
    have hnot : D x ∉ L := fun h => hout (hLs h)
    have heq : D x = x := D.injective (hD (D x) hnot)
    exact hout (heq.symm ▸ hx)
  have hFt (t : Real) := hmaps (F t) (hFfix t)
  have hFit (t : Real) := hmaps (F t).symm (hfixsymm t)
  let U : Opens M := ⟨e.target, e.open_target⟩
  let K : Set M := e '' L
  have hK : IsCompact K := hL.image_of_continuousOn (he.continuousOn.mono hLs)
  have hKU : K ⊆ e.target := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_source (hLs hy)
  let g (t : Real) (y : U) : U :=
    ⟨e (F t (e.symm y)), e.map_source (hFt t (e.map_target y.property))⟩
  let gi (t : Real) (y : U) : U :=
    ⟨e ((F t).symm (e.symm y)), e.map_source (hFit t (e.map_target y.property))⟩
  have hg (t : Real) : ContMDiff I I ∞ (g t) := by
    intro y
    apply (ContMDiffAt.subtypeVal_comp_iff U (g t) y).mp
    change ContMDiffAt I I ∞ (fun z : U => e (F t (e.symm z))) y
    exact (he.contMDiffAt (e.open_source.mem_nhds
      (hFt t (e.map_target y.property)))).comp y
      ((F t).contMDiff.contMDiffAt.comp y
        ((hei.contMDiffAt (e.open_target.mem_nhds y.property)).comp y
          contMDiff_subtype_val.contMDiffAt))
  have hgi (t : Real) : ContMDiff I I ∞ (gi t) := by
    intro y
    apply (ContMDiffAt.subtypeVal_comp_iff U (gi t) y).mp
    change ContMDiffAt I I ∞ (fun z : U => e ((F t).symm (e.symm z))) y
    exact (he.contMDiffAt (e.open_source.mem_nhds
      (hFit t (e.map_target y.property)))).comp y
      ((F t).symm.contMDiff.contMDiffAt.comp y
        ((hei.contMDiffAt (e.open_target.mem_nhds y.property)).comp y
          contMDiff_subtype_val.contMDiffAt))
  let G (t : Real) : Diffeomorph I I U U ∞ := {
    toEquiv := {
      toFun := g t
      invFun := gi t
      left_inv := by
        intro y
        apply Subtype.ext
        change e ((F t).symm (e.symm (e (F t (e.symm y))))) = y
        rw [e.left_inv (hFt t (e.map_target y.property)), (F t).symm_apply_apply,
          e.right_inv y.property]
      right_inv := by
        intro y
        apply Subtype.ext
        change e (F t (e.symm (e ((F t).symm (e.symm y))))) = y
        rw [e.left_inv (hFit t (e.map_target y.property)), (F t).apply_symm_apply,
          e.right_inv y.property] }
    contMDiff_toFun := hg t
    contMDiff_invFun := hgi t }
  have hGfix (t : Real) (y : U) (hy : (y : M) ∉ K) : G t y = y := by
    have hx : e.symm y ∉ L := by
      intro hx
      exact hy ⟨e.symm y, hx, e.right_inv y.property⟩
    apply Subtype.ext
    change e (F t (e.symm y)) = y
    rw [hFfix t _ hx, e.right_inv y.property]
  have hex (t : Real) := Diffeomorph.exists_extension_of_isCompact U (G t) hK hKU (hGfix t)
  choose Phi hPhi hPhifix using hex
  have hcoord (t : Real) (y : M) (hy : y ∈ e.target) :
      Phi t y = e (F t (e.symm y)) := hPhi t ⟨y, hy⟩
  have hPhi0 (y : M) : Phi 0 y = y := by
    by_cases hy : y ∈ e.target
    · rw [hcoord 0 y hy, hF0, e.right_inv hy]
    · exact hPhifix 0 y (fun h => hy (hKU h))
  have hsmooth : ContMDiff (𝓘(Real, Real).prod I) I ∞
      (fun p : Real × M => Phi p.1 p.2) := by
    have hFm : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, E)) 𝓘(Real, E) ∞
        (fun p : Real × E => F p.1 p.2) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hFs.contMDiff
    intro p
    by_cases hp : p.2 ∈ e.target
    · have harg : ContMDiffAt (𝓘(Real, Real).prod I)
          (𝓘(Real, Real).prod 𝓘(Real, E)) ∞
          (fun q : Real × M => (q.1, e.symm q.2)) p :=
        contMDiffAt_fst.prodMk
          ((hei.contMDiffAt (e.open_target.mem_nhds hp)).comp p contMDiffAt_snd)
      have hinner := hFm.contMDiffAt.comp p harg
      have hwhole := (he.contMDiffAt (e.open_source.mem_nhds
        (hFt p.1 (e.map_target hp)))).comp p hinner
      apply hwhole.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (e.open_target.mem_nhds hp)] with q hq
      exact hcoord q.1 q.2 hq
    · have hpK : p.2 ∉ K := fun h => hp (hKU h)
      apply contMDiffAt_snd.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (hK.isClosed.isOpen_compl.mem_nhds hpK)] with q hq
      exact hPhifix q.1 q.2 hq
  refine ⟨hK, hKU, Phi, hPhi0, hsmooth, hPhifix, ?_⟩
  intro t x hx
  rw [hcoord t (e x) (e.map_source hx), e.left_inv hx]

end Poincare.Manifold.Schoenflies
