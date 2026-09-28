import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Height
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P := E2 × Real

private theorem exists_partialDiffeomorph_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace E] [CompleteSpace F]
    {g : E -> F} {s : Set E} (hs : IsOpen s) (hg : ContDiffOn Real ∞ g s)
    {a : E} (ha : a ∈ s) (hb : Function.Bijective (fderiv Real g a)) :
    ∃ d : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, F) E F ∞,
      a ∈ d.source ∧ d.source ⊆ s ∧ (d : E -> F) = g := by
  let A := ContinuousLinearEquiv.ofBijective (fderiv Real g a)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hga : ContDiffAt Real ∞ g a := hg.contDiffAt (hs.mem_nhds ha)
  have hd : HasFDerivAt g A.toContinuousLinearMap a :=
    (hga.differentiableAt (by simp)).hasFDerivAt
  let U := s ∩ (fderiv Real g) ⁻¹'
    range (fun B : E ≃L[Real] F => B.toContinuousLinearMap)
  have hU : IsOpen U :=
    (hg.continuousOn_fderiv_of_isOpen hs (by simp)).isOpen_inter_preimage hs
      ContinuousLinearEquiv.isOpen
  let Q := hga.toOpenPartialHomeomorph g hd (by simp)
  let H := Q.restr U
  have hHsource : H.source ⊆ U := fun _ hz => interior_subset hz.2
  have hHa : a ∈ H.source := by
    rw [Q.restr_source' U hU]
    exact ⟨hga.mem_toOpenPartialHomeomorph_source hd (by simp), ha, A, rfl⟩
  have hHi : ContMDiffOn 𝓘(Real, F) 𝓘(Real, E) ∞ H.symm H.target := by
    intro y hy
    have hz := hHsource (H.map_target hy)
    obtain ⟨B, hB⟩ := hz.2
    dsimp only at hB
    have hgz : ContDiffAt Real ∞ g (H.symm y) := hg.contDiffAt (hs.mem_nhds hz.1)
    have hdB : HasFDerivAt H B.toContinuousLinearMap (H.symm y) := by
      change HasFDerivAt g B.toContinuousLinearMap (H.symm y)
      rw [hB]
      exact (hgz.differentiableAt (by simp)).hasFDerivAt
    exact (H.contDiffAt_symm hy hdB hgz).contMDiffWithinAt.mono (subset_univ _)
  let d : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, F) E F ∞ := {
    toPartialEquiv := H.toPartialEquiv
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := (hg.mono (fun _ hz => (hHsource hz).1)).contMDiffOn
    contMDiffOn_invFun := hHi }
  exact ⟨d, hHa, fun _ hz => (hHsource hz).1, rfl⟩

theorem bijective_fderiv_vertical_height_coordinates
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    Function.Bijective (fderiv Real (fun z : P => f (e z.1) + z.2 • (v : E3)) 0) := by
  let d : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hei }
  have heloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ e 0 :=
    ⟨d, he0, fun _ _ => rfl⟩
  have hebij : Function.Bijective (mfderiv (𝓡 2) (𝓡 2) e 0) :=
    (heloc.mfderivToContinuousLinearEquiv (by simp)).bijective
  let g : E2 -> E3 := f ∘ e
  have hg : ContDiffAt Real ∞ g 0 :=
    ((hf.contMDiff (e 0)).comp 0 heloc.contMDiffAt).contDiffAt
  have hchain (u : E2) : fderiv Real g 0 u =
      mfderiv (𝓡 2) (𝓡 3) f p (mfderiv (𝓡 2) (𝓡 2) e 0 u) := by
    have h := mfderiv_comp 0
      ((hf.contMDiff (e 0)).mdifferentiableAt (by simp))
      (heloc.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, hep] at h
    exact congrArg (fun L : E2 →L[Real] E3 => L u) h
  have hinj : Function.Injective (fderiv Real g 0) := by
    intro u w huw
    apply hebij.injective
    apply injective_mfderiv_sphere_embedding hf p
    simpa only [hchain] using huw
  have horth (u : E2) : inner Real (v : E3) (fderiv Real g 0 u) = 0 := by
    rw [hchain, ← mfderiv_height_apply hf.contMDiff, hp]
    rfl
  have hderiv : fderiv Real (fun z : P => f (e z.1) + z.2 • (v : E3)) 0 =
      (fderiv Real g 0).comp (ContinuousLinearMap.fst Real E2 Real) +
        (ContinuousLinearMap.snd Real E2 Real).smulRight (v : E3) := by
    exact (((hg.differentiableAt (by simp)).hasFDerivAt.comp (0 : P)
      (hasFDerivAt_fst)).add
      ((hasFDerivAt_snd : HasFDerivAt (Prod.snd : P -> Real)
        (ContinuousLinearMap.snd Real E2 Real) (0 : P)).smul_const (v : E3))).fderiv
  have hderiv_apply (z : P) :
      fderiv Real (fun z : P => f (e z.1) + z.2 • (v : E3)) 0 z =
        fderiv Real g 0 z.1 + z.2 • (v : E3) := by
    rw [hderiv]
    rfl
  have hi : Function.Injective
      (fderiv Real (fun z : P => f (e z.1) + z.2 • (v : E3)) 0) := by
    intro z w hzw
    have hz : inner Real (v : E3) (v : E3) = 1 := by simp
    have ht : z.2 = w.2 := by
      have h := congrArg (fun y : E3 => inner Real (v : E3) y) hzw
      simpa only [hderiv_apply, inner_add_right, inner_smul_right, horth,
        hz, mul_one, zero_add] using h
    apply Prod.ext (hinj ?_) ht
    simpa only [hderiv_apply, ht, add_left_inj] using hzw
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    simp [P, E2, E3, Module.finrank_prod])).mp hi⟩

theorem exists_ambient_height_coordinates
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    ∃ F : OpenPartialHomeomorph P E3,
      0 ∈ F.source ∧ F.source ⊆ e.source ×ˢ univ ∧ F 0 = f p ∧
      ContDiffOn Real ∞ F F.source ∧ ContDiffOn Real ∞ F.symm F.target ∧
      ∀ z ∈ F.source, F z = f (e z.1) + z.2 • (v : E3) := by
  let G : P -> E3 := fun z => f (e z.1) + z.2 • (v : E3)
  have hG : ContDiffOn Real ∞ G (e.source ×ˢ univ) := by
    have hg : ContDiffOn Real ∞ (f ∘ e) e.source :=
      (hf.contMDiff.comp_contMDiffOn he).contDiffOn
    exact (hg.comp contDiffOn_fst (fun _ hz => hz.1)).add
      (contDiffOn_snd.smul contDiffOn_const)
  obtain ⟨d, hd0, hds, hdG⟩ := exists_partialDiffeomorph_of_contDiffOn
    (e.open_source.prod isOpen_univ) hG (show (0 : P) ∈ e.source ×ˢ univ from ⟨he0, trivial⟩)
    (bijective_fderiv_vertical_height_coordinates hf v p hp e he0 hep he hei)
  refine ⟨d.toOpenPartialHomeomorph, hd0, hds, ?_,
    d.contMDiffOn_toFun.contDiffOn, d.contMDiffOn_invFun.contDiffOn, ?_⟩
  · change d 0 = f p
    rw [hdG]
    simp [G, hep]
  · intro z _
    change d z = G z
    rw [hdG]

theorem exists_ambient_morse_coordinates
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 -> Real)
    (hform : ∀ x ∈ e.source, inner Real (v : E3) (f (e x)) =
      inner Real (v : E3) (f p) + ∑ i : Fin 2, σ i * x i ^ 2) :
    ∃ F : OpenPartialHomeomorph P E3,
      0 ∈ F.source ∧ F.source ⊆ e.source ×ˢ univ ∧ F 0 = f p ∧
      ContDiffOn Real ∞ F F.source ∧ ContDiffOn Real ∞ F.symm F.target ∧
      (∀ z ∈ F.source, F z = f (e z.1) + z.2 • (v : E3)) ∧
      ∀ z ∈ F.source, inner Real (v : E3) (F z) =
        inner Real (v : E3) (f p) + (∑ i : Fin 2, σ i * z.1 i ^ 2) + z.2 := by
  obtain ⟨F, hF0, hFs, hFp, hF, hFi, hFeq⟩ :=
    exists_ambient_height_coordinates hf v p hp e he0 hep he hei
  refine ⟨F, hF0, hFs, hFp, hF, hFi, hFeq, ?_⟩
  intro z hz
  rw [hFeq z hz, inner_add_right, inner_smul_right, hform z.1 (hFs hz).1]
  simp

end Poincare.Manifold.Schoenflies
