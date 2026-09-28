import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_compact_chart_diffeomorph_family
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ F H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] (T : OpenPartialHomeomorph M E) (htarget : T.target = univ)
    (hT : ContMDiffOn I 𝓘(ℝ, E) ∞ T T.source)
    (hInv : ContMDiff 𝓘(ℝ, E) I ∞ T.symm)
    (D : ℝ → E ≃ₘ[ℝ] E)
    (hD : ContDiff ℝ ∞ (fun p : ℝ × E => D p.1 p.2))
    (hDI : ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1).symm p.2))
    {K : Set E} (hK : IsCompact K) (hfix : ∀ t x, x ∉ K → D t x = x) :
    ∃ A : ℝ → M ≃ₘ⟮I, I⟯ M,
      (∀ t x, x ∈ T.source → A t x = T.symm (D t (T x))) ∧
      (∀ t x, x ∈ T.source → (A t).symm x = T.symm ((D t).symm (T x))) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => A p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (A p.1).symm p.2) ∧
      IsCompact (T.symm '' K) ∧
      (∀ t x, x ∉ T.symm '' K → A t x = x ∧ (A t).symm x = x) := by
  classical
  have hright (x : E) : T (T.symm x) = x := T.right_inv (htarget ▸ mem_univ x)
  have hsource (x : E) : T.symm x ∈ T.source := T.map_target (htarget ▸ mem_univ x)
  have hfixInv (t : ℝ) (x : E) (hx : x ∉ K) : (D t).symm x = x := by
    have h := congrArg (D t).symm (hfix t x hx)
    simpa only [(D t).symm_apply_apply] using h.symm
  let C : (E → E) → M → M := fun f x =>
    if x ∈ T.source then T.symm (f (T x)) else x
  have hCapply (f : E → E) (x : M) (hx : x ∈ T.source) :
      C f x = T.symm (f (T x)) := by simp only [C, if_pos hx]
  have hCfix (f : E → E) (hf : ∀ x, x ∉ K → f x = x)
      (x : M) (hx : x ∉ T.symm '' K) : C f x = x := by
    by_cases ht : x ∈ T.source
    · have hnK : T x ∉ K := fun h => hx ⟨T x, h, T.left_inv ht⟩
      rw [hCapply f x ht, hf _ hnK, T.left_inv ht]
    · simp only [C, if_neg ht]
  have hCleft (f g : E → E) (hgf : LeftInverse g f) :
      LeftInverse (C g) (C f) := by
    intro x
    by_cases hx : x ∈ T.source
    · have hs : C f x ∈ T.source := by rw [hCapply f x hx]; exact hsource _
      rw [hCapply g _ hs, hCapply f x hx, hright, hgf, T.left_inv hx]
    · simp only [C, if_neg hx]
  have himage : IsCompact (T.symm '' K) := hK.image hInv.continuous
  have hCsmooth (f : ℝ → E → E)
      (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
      (hffix : ∀ t x, x ∉ K → f t x = x) :
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => C (f p.1) p.2) := by
    intro p
    by_cases hx : p.2 ∈ T.source
    · have hTx : ContMDiffAt I 𝓘(ℝ, E) ∞ T p.2 :=
        hT.contMDiffAt (T.open_source.mem_nhds hx)
      have hinner : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
          (fun q : ℝ × M => (q.1, T q.2)) p :=
        contMDiffAt_fst.prodMk_space (hTx.comp p contMDiffAt_snd)
      have hs := hInv.contMDiffAt.comp p (hf.contMDiff.contMDiffAt.comp p hinner)
      apply hs.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (T.open_source.mem_nhds hx)] with q hq
      exact hCapply (f q.1) q.2 hq
    · have hn : p.2 ∉ T.symm '' K := by
        rintro ⟨y, hy, heq⟩
        exact hx (heq ▸ hsource y)
      apply contMDiffAt_snd.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (himage.isClosed.isOpen_compl.mem_nhds hn)] with q hq
      exact hCfix (f q.1) (hffix q.1) q.2 hq
  have hCF := hCsmooth (fun t => D t) hD hfix
  have hCI := hCsmooth (fun t => (D t).symm) hDI hfixInv
  let A : ℝ → M ≃ₘ⟮I, I⟯ M := fun t =>
    { toEquiv :=
        { toFun := C (D t)
          invFun := C (D t).symm
          left_inv := hCleft (D t) (D t).symm (D t).symm_apply_apply
          right_inv := hCleft (D t).symm (D t) (D t).apply_symm_apply }
      contMDiff_toFun := hCF.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hCI.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨A, fun t x hx => hCapply (D t) x hx,
    fun t x hx => hCapply (D t).symm x hx, hCF, hCI, himage, ?_⟩
  intro t x hx
  exact ⟨hCfix (D t) (hfix t) x hx, hCfix (D t).symm (hfixInv t) x hx⟩

end PoincareConjecture.M25.Topology3D
