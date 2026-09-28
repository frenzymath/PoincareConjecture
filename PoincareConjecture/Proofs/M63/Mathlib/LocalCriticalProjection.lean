import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M63

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hasFDerivAt_criticalProjection {f : E → F} {c : E}
    (hf : ContDiffAt ℝ 2 f c) :
    HasFDerivAt (fun p : F × E => (fderiv ℝ f p.2).adjoint (p.1 - f p.2))
      ((fderiv ℝ f c).adjoint.comp
        (ContinuousLinearMap.fst ℝ F E -
          (fderiv ℝ f c).comp (ContinuousLinearMap.snd ℝ F E))) (f c, c) := by
  let ad : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hdf : DifferentiableAt ℝ (fun p : F × E => ad (fderiv ℝ f p.2)) (f c, c) :=
    ad.differentiableAt.comp _
      (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp _
        differentiableAt_snd)
  have hr : HasFDerivAt (fun p : F × E => p.1 - f p.2)
      (ContinuousLinearMap.fst ℝ F E -
        (fderiv ℝ f c).comp (ContinuousLinearMap.snd ℝ F E)) (f c, c) :=
    hasFDerivAt_fst.sub
      ((hf.differentiableAt (by norm_num)).hasFDerivAt.comp _ hasFDerivAt_snd)
  convert! hdf.hasFDerivAt.clm_apply hr using 1
  simp only [sub_self, map_zero, add_zero, ad]
  rfl

theorem exists_local_criticalProjection [FiniteDimensional ℝ E]
    {f : E → F} {s : Set E} {c : E} (hs : IsOpen s) (hc : c ∈ s)
    (hf : ContDiffOn ℝ ∞ f s) (hinj : Function.Injective (fderiv ℝ f c)) :
    ∃ W : Set F, ∃ V : Set E, ∃ g : F → E,
      IsOpen W ∧ f c ∈ W ∧ IsOpen V ∧ c ∈ V ∧ V ⊆ s ∧
      g (f c) = c ∧ MapsTo g W V ∧ ContDiffOn ℝ ∞ g W ∧
      (∀ z ∈ W, (fderiv ℝ f (g z)).adjoint (z - f (g z)) = 0) ∧
      ∀ z ∈ W, ∀ u ∈ V, (fderiv ℝ f u).adjoint (z - f u) = 0 → u = g z := by
  let A := fderiv ℝ f c
  let K := A.adjoint.comp A
  have hKi : Function.Injective K := A.adjoint_comp_self_injective_iff.mpr hinj
  let J : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo K.toLinearMap hKi).toContinuousLinearEquiv
  let fst := ContinuousLinearMap.fst ℝ F E
  let snd := ContinuousLinearMap.snd ℝ F E
  let B0 := fst.prod (A.adjoint.comp (fst - A.comp snd))
  let C0 := fst.prod (J.symm.toContinuousLinearMap.comp (A.adjoint.comp fst - snd))
  have hleft : Function.LeftInverse C0 B0 := by
    intro q
    apply Prod.ext
    · rfl
    · change J.symm (A.adjoint q.1 - A.adjoint (q.1 - A q.2)) = q.2
      rw [map_sub A.adjoint, sub_sub_cancel]
      exact J.symm_apply_apply q.2
  have hright : Function.RightInverse C0 B0 := by
    intro q
    apply Prod.ext
    · rfl
    · change A.adjoint (q.1 - A (J.symm (A.adjoint q.1 - q.2))) = q.2
      rw [map_sub]
      change A.adjoint q.1 - J (J.symm (A.adjoint q.1 - q.2)) = q.2
      rw [J.apply_symm_apply, sub_sub_cancel]
  let B := ContinuousLinearEquiv.equivOfInverse B0 C0 hleft hright
  let P (q : F × E) := (fderiv ℝ f q.2).adjoint (q.1 - f q.2)
  let H (q : F × E) := (q.1, P q)
  let S : Set (F × E) := univ ×ˢ s
  let p : F × E := (f c, c)
  have hS : IsOpen S := isOpen_univ.prod hs
  have hpS : p ∈ S := ⟨mem_univ _, hc⟩
  let ad : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hfs : ContDiffOn ℝ ∞ (fun q : F × E => f q.2) S :=
    hf.comp contDiffOn_snd (fun _ hq => hq.2)
  have hdf : ContDiffOn ℝ ∞ (fun q : F × E => fderiv ℝ f q.2) S :=
    (hf.fderiv_of_isOpen hs (by simp)).comp contDiffOn_snd (fun _ hq => hq.2)
  have hP : ContDiffOn ℝ ∞ P S := by
    convert! (ad.contDiff.comp_contDiffOn hdf).clm_apply (contDiffOn_fst.sub hfs) using 1
  have hH : ContDiffOn ℝ ∞ H S := contDiffOn_fst.prodMk hP
  have hHp : ContDiffAt ℝ ∞ H p := hH.contDiffAt (hS.mem_nhds hpS)
  have hB : HasFDerivAt H (B : F × E →L[ℝ] F × E) p := by
    convert! hasFDerivAt_fst.prodMk (hasFDerivAt_criticalProjection
      ((hf.contDiffAt (hs.mem_nhds hc)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))) using 1
  let h := hHp.toOpenPartialHomeomorph H hB (by simp)
  have hcoe : (h : (F × E) → F × E) = H := rfl
  have hp : p ∈ h.source := hHp.mem_toOpenPartialHomeomorph_source hB (by simp)
  have hbase : h p = (f c, 0) := by
    change (f c, (fderiv ℝ f c).adjoint (f c - f c)) = (f c, 0)
    rw [sub_self, map_zero]
  have hbaseinv : h.symm (f c, 0) = p := by rw [← hbase, h.left_inv hp]
  have htarget : (f c, 0) ∈ h.target := hbase ▸ h.map_source hp
  have hdercont : ContinuousAt (fderiv ℝ H) p :=
    (hH.continuousOn_fderiv_of_isOpen hS (by simp)).continuousAt (hS.mem_nhds hpS)
  have hInv : {q | ∃ e : (F × E) ≃L[ℝ] (F × E), e.toContinuousLinearMap = fderiv ℝ H q}
      ∈ 𝓝 p := by
    change (fderiv ℝ H) ⁻¹' range
      (fun e : (F × E) ≃L[ℝ] (F × E) => e.toContinuousLinearMap) ∈ 𝓝 p
    apply hdercont.preimage_mem_nhds
    rw [hB.fderiv]
    exact B.nhds
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hInv (Filter.inter_mem (h.open_source.mem_nhds hp) (hS.mem_nhds hpS)))
  obtain ⟨W0, V, hW0, hcW0, hV, hcV, hprod⟩ := mem_nhds_prod_iff'.mp (hO.mem_nhds hpO)
  let T := h.target ∩ h.symm ⁻¹' (O ∩ (univ ×ˢ V))
  have hT : IsOpen T := h.isOpen_inter_preimage_symm (hO.inter (isOpen_univ.prod hV))
  have hpT : (f c, 0) ∈ T := by
    refine ⟨htarget, ?_⟩
    change h.symm (f c, 0) ∈ O ∩ (univ ×ˢ V)
    rw [hbaseinv]
    exact ⟨hpO, mem_univ _, hcV⟩
  let W := W0 ∩ (fun z : F => (z, (0 : E))) ⁻¹' T
  let g (z : F) := (h.symm (z, 0)).2
  have hW : IsOpen W := hW0.inter (hT.preimage (continuous_id.prodMk continuous_const))
  have hcW : f c ∈ W := ⟨hcW0, hpT⟩
  have hVs : V ⊆ s := by
    intro u hu
    exact (hOsub (hprod (show (f c, u) ∈ W0 ×ˢ V from ⟨hcW0, hu⟩))).2.2.2
  have hgbase : g (f c) = c := congrArg Prod.snd hbaseinv
  have hgV : MapsTo g W V := fun _ hz => hz.2.2.2.2
  have hgsmooth : ContDiffOn ℝ ∞ g W := by
    intro z hz
    have hqO : h.symm (z, 0) ∈ O := hz.2.2.1
    have hqS : h.symm (z, 0) ∈ S := (hOsub hqO).2.2
    have hHq := hH.contDiffAt (hS.mem_nhds hqS)
    obtain ⟨e, he⟩ := (hOsub hqO).1
    have hqe : HasFDerivAt h e.toContinuousLinearMap (h.symm (z, 0)) := by
      rw [hcoe, he]
      exact (hHq.differentiableAt (by simp)).hasFDerivAt
    have hi := h.contDiffAt_symm (f₀' := e) hz.2.1 hqe
      (by simpa only [hcoe] using hHq)
    exact (contDiffAt_snd.comp z
      (hi.comp z (contDiffAt_id.prodMk contDiffAt_const))).contDiffWithinAt
  have hcritical (z : F) (hz : z ∈ W) : P (z, g z) = 0 := by
    have hright' : H (h.symm (z, 0)) = (z, 0) := h.right_inv hz.2.1
    have hfst : (h.symm (z, 0)).1 = z := congrArg Prod.fst hright'
    have hsnd : P (h.symm (z, 0)) = 0 := congrArg Prod.snd hright'
    have hpair : (z, g z) = h.symm (z, 0) := Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  refine ⟨W, V, g, hW, hcW, hV, hcV, hVs, hgbase, hgV, hgsmooth, hcritical, ?_⟩
  intro z hz u hu hcrit
  have hzu : (z, u) ∈ h.source := (hOsub (hprod ⟨hz.1, hu⟩)).2.1
  have hvalue : h (z, u) = (z, 0) := by
    change (z, P (z, u)) = (z, 0)
    rw [show P (z, u) = 0 from hcrit]
  have hback := h.left_inv hzu
  rw [hvalue] at hback
  exact (congrArg Prod.snd hback).symm

end PoincareConjecture.M63
