import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Topology












set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M65Boundary

open Classical in
private theorem homeomorph_closed_replacement
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (h : X ≃ₜ Y) (A : Set X) (hA : IsClosed A)
    (L : X → Y) (hL : ContinuousOn L A) (hfront : EqOn L h (frontier A))
    (hinj : InjOn L A) (himage : L '' A = h '' A) :
    ∃ H : X ≃ₜ Y, ∀ x, H x = if x ∈ A then L x else h x := by
  classical
  let F : X → Y := A.piecewise L h
  have hc : Continuous F := continuous_piecewise hfront
    (by rwa [hA.closure_eq]) h.continuous.continuousOn
  have hi : Function.Injective F := by
    intro x y hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · exact hinj hx hy (by simp only [F, piecewise, hx, hy, ↓reduceIte] at hxy; exact hxy)
    · have he : L x = h y := by
        simpa only [F, piecewise, hx, hy, ↓reduceIte] using hxy
      have hm : h y ∈ h '' A := himage ▸ (he ▸ mem_image_of_mem L hx)
      obtain ⟨z, hz, hzy⟩ := hm
      exact (hy (h.injective hzy ▸ hz)).elim
    · have he : h x = L y := by
        simpa only [F, piecewise, hx, hy, ↓reduceIte] using hxy
      have hm : h x ∈ h '' A := himage ▸ (he.symm ▸ mem_image_of_mem L hy)
      obtain ⟨z, hz, hzx⟩ := hm
      exact (hx (h.injective hzx ▸ hz)).elim
    · exact h.injective (by simpa only [F, piecewise, hx, hy, ↓reduceIte] using hxy)
  have hs : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    by_cases hx : x ∈ A
    · have hm : h x ∈ L '' A := himage.symm ▸ mem_image_of_mem h hx
      obtain ⟨z, hz, he⟩ := hm
      exact ⟨z, by simpa only [F, piecewise, hz, ↓reduceIte] using he⟩
    · exact ⟨x, by simp only [F, piecewise, hx, ↓reduceIte]⟩
  let H : X ≃ₜ Y := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective F ⟨hi, hs⟩) hc
  exact ⟨H, fun _ => rfl⟩

open Classical in



def traceInterpolation (A : Set LoopCircle) (q : LoopCircle → ℝ)
    (s : ℝ → LoopCircle) (E : OpenPartialHomeomorph LoopCircle ℝ)
    (f : LoopCircle → LoopCircle) (z : LoopCircle) : LoopCircle :=
  if z ∈ A then E.symm (AffineMap.lineMap (E (f (s 0))) (E (f (s 1))) (q z)) else f z

private theorem interpolation_target
    (E : OpenPartialHomeomorph LoopCircle ℝ) (hconv : Convex ℝ E.target)
    {u v : LoopCircle} (hu : u ∈ E.source) (hv : v ∈ E.source)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap (E u) (E v) t ∈ E.target :=
  hconv.mapsTo_lineMap (E.map_source hu) (E.map_source hv) ht





theorem traceInterpolation_homeomorph
    (A : Set LoopCircle) (hA : IsClosed A)
    (q : LoopCircle → ℝ) (s : ℝ → LoopCircle)
    (hq : ContinuousOn q A) (hs : ContinuousOn s (Icc (0 : ℝ) 1))
    (hqA : MapsTo q A (Icc (0 : ℝ) 1))
    (hsA : MapsTo s (Icc (0 : ℝ) 1) A)
    (hqs : ∀ t ∈ Icc (0 : ℝ) 1, q (s t) = t)
    (hsq : ∀ z ∈ A, s (q z) = z)
    (hfront : ∀ z ∈ frontier A, q z = 0 ∨ q z = 1)
    (E : OpenPartialHomeomorph LoopCircle ℝ) (hconv : Convex ℝ E.target)
    (h : LoopCircle ≃ₜ LoopCircle) (hcap : MapsTo h A E.source) :
    ∃ H : LoopCircle ≃ₜ LoopCircle, ∀ z, H z = traceInterpolation A q s E h z := by
  classical
  have hs0 : s 0 ∈ A := hsA (by norm_num)
  have hs1 : s 1 ∈ A := hsA (by norm_num)
  let f : ℝ → ℝ := fun t => E (h (s t))
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    E.continuousOn.comp (h.continuous.comp_continuousOn hs) (hcap.comp hsA)
  have hfi : InjOn f (Icc (0 : ℝ) 1) := by
    intro t ht u hu heq
    have he := h.injective (E.injOn (hcap (hsA ht)) (hcap (hsA hu)) heq)
    simpa only [hqs t ht, hqs u hu] using congrArg q he
  have hends : f 0 ≠ f 1 := fun he =>
    (by norm_num : (0 : ℝ) ≠ 1) (hfi (by norm_num) (by norm_num) he)
  have himage : f '' Icc (0 : ℝ) 1 = uIcc (f 0) (f 1) := by
    rcases hfc.strictMonoOn_of_injOn_Icc' (by norm_num) hfi with hm | hm
    · rw [hfc.image_Icc_of_monotoneOn (by norm_num) hm.monotoneOn,
        uIcc_of_le (hm.monotoneOn (by norm_num) (by norm_num) (by norm_num))]
    · rw [hfc.image_Icc_of_antitoneOn (by norm_num) hm.antitoneOn,
        uIcc_of_ge (hm.antitoneOn (by norm_num) (by norm_num) (by norm_num))]
  let L : LoopCircle → LoopCircle := fun z => E.symm
    (AffineMap.lineMap (f 0) (f 1) (q z))
  have hLt (z : LoopCircle) (hz : z ∈ A) :
      AffineMap.lineMap (f 0) (f 1) (q z) ∈ E.target :=
    interpolation_target E hconv (hcap hs0) (hcap hs1) (hqA hz)
  have hLc : ContinuousOn L A :=
    E.symm.continuousOn.comp (AffineMap.lineMap_continuous.comp_continuousOn hq) hLt
  have hLf : EqOn L h (frontier A) := by
    intro z hz
    have hzA : z ∈ A := hA.closure_eq ▸ frontier_subset_closure hz
    have he := hsq z hzA
    rcases hfront z hz with hzq | hzq <;>
      dsimp only [L] <;> rw [hzq] at he ⊢
    · rw [AffineMap.lineMap_apply_zero]
      exact (E.left_inv (hcap hs0)).trans (congrArg h he)
    · rw [AffineMap.lineMap_apply_one]
      exact (E.left_inv (hcap hs1)).trans (congrArg h he)
  have hLi : InjOn L A := by
    intro z hz w hw he
    have heq := (E.symm.injOn (hLt z hz) (hLt w hw)) he
    have hqeq := AffineMap.lineMap_injective ℝ hends heq
    exact (hsq z hz).symm.trans ((congrArg s hqeq).trans (hsq w hw))
  have hLim : L '' A = h '' A := by
    have hqim : q '' A = Icc (0 : ℝ) 1 := by
      apply Subset.antisymm hqA.image_subset
      intro t ht
      exact ⟨s t, hsA ht, hqs t ht⟩
    have hsimage : s '' Icc (0 : ℝ) 1 = A := by
      apply Subset.antisymm hsA.image_subset
      intro z hz
      exact ⟨q z, hqA hz, hsq z hz⟩
    calc
      _ = E.symm '' (AffineMap.lineMap (f 0) (f 1) '' (q '' A)) := by
        simp only [image_image, L]
      _ = E.symm '' uIcc (f 0) (f 1) := by
        rw [hqim, ← segment_eq_image_lineMap, segment_eq_uIcc]
      _ = E.symm '' (f '' Icc (0 : ℝ) 1) := by rw [himage]
      _ = (fun t => h (s t)) '' Icc (0 : ℝ) 1 := by
        rw [image_image]
        exact image_congr (fun t ht => E.left_inv (hcap (hsA ht)))
      _ = _ := by rw [← image_image, hsimage]
  obtain ⟨H, hH⟩ := homeomorph_closed_replacement h A hA L hLc hLf hLi hLim
  exact ⟨H, hH⟩

set_option maxHeartbeats 1200000 in





theorem traceInterpolation_joint_continuous
    (A : Set LoopCircle) (hA : IsClosed A)
    (q : LoopCircle → ℝ) (s : ℝ → LoopCircle)
    (hq : ContinuousOn q A) (hqA : MapsTo q A (Icc (0 : ℝ) 1))
    (hsA : MapsTo s (Icc (0 : ℝ) 1) A)
    (hsq : ∀ z ∈ A, s (q z) = z)
    (hfront : ∀ z ∈ frontier A, q z = 0 ∨ q z = 1)
    (E : OpenPartialHomeomorph LoopCircle ℝ) (hconv : Convex ℝ E.target) :
    ContinuousOn (fun p : C(LoopCircle, LoopCircle) × LoopCircle =>
      traceInterpolation A q s E p.1 p.2)
      ({f : C(LoopCircle, LoopCircle) | MapsTo f A E.source} ×ˢ univ) := by
  classical
  let V : Set C(LoopCircle, LoopCircle) := {f | MapsTo f A E.source}
  let D : Set (C(LoopCircle, LoopCircle) × LoopCircle) := Prod.snd ⁻¹' A
  let L (p : C(LoopCircle, LoopCircle) × LoopCircle) :=
    E.symm (AffineMap.lineMap (E (p.1 (s 0))) (E (p.1 (s 1))) (q p.2))
  have hs0 : s 0 ∈ A := hsA (by norm_num)
  have hs1 : s 1 ∈ A := hsA (by norm_num)
  have hD : IsClosed D := hA.preimage continuous_snd
  have h0 : ContinuousOn (fun p : C(LoopCircle, LoopCircle) × LoopCircle => E (p.1 (s 0)))
      (V ×ˢ A) := E.continuousOn.comp
        ((continuous_eval_const (s 0)).comp continuous_fst).continuousOn (fun p hp => hp.1 hs0)
  have h1 : ContinuousOn (fun p : C(LoopCircle, LoopCircle) × LoopCircle => E (p.1 (s 1)))
      (V ×ˢ A) := E.continuousOn.comp
        ((continuous_eval_const (s 1)).comp continuous_fst).continuousOn (fun p hp => hp.1 hs1)
  have hq' : ContinuousOn (fun p : C(LoopCircle, LoopCircle) × LoopCircle => q p.2)
      (V ×ˢ A) := hq.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hLc : ContinuousOn L (V ×ˢ A) := E.symm.continuousOn.comp
    (AffineMap.lineMap_continuous_uncurry.comp_continuousOn (h0.prodMk (h1.prodMk hq')))
    (fun p hp => interpolation_target E hconv (hp.1 hs0) (hp.1 hs1) (hqA hp.2))
  have hLf : ∀ p ∈ (V ×ˢ univ) ∩ frontier D, L p = p.1 p.2 := by
    intro p hp
    have hz : p.2 ∈ frontier A := continuous_snd.frontier_preimage_subset A hp.2
    have hzA : p.2 ∈ A := hA.closure_eq ▸ frontier_subset_closure hz
    have he := hsq p.2 hzA
    rcases hfront p.2 hz with hzq | hzq <;>
      dsimp only [L] <;> rw [hzq] at he ⊢
    · rw [AffineMap.lineMap_apply_zero]
      exact (E.left_inv (hp.1.1 hs0)).trans (congrArg p.1 he)
    · rw [AffineMap.lineMap_apply_one]
      exact (E.left_inv (hp.1.1 hs1)).trans (congrArg p.1 he)
  have hpart : (V ×ˢ univ) ∩ closure D = V ×ˢ A := by
    rw [hD.closure_eq]
    ext p
    simp only [D, mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage]
  have hh := ContinuousOn.piecewise (t := D) hLf (hpart ▸ hLc)
    (continuous_eval.continuousOn : ContinuousOn
      (fun p : C(LoopCircle, LoopCircle) × LoopCircle => p.1 p.2) ((V ×ˢ univ) ∩ closure Dᶜ))
  exact hh

set_option maxHeartbeats 1200000 in






theorem weak_parameter_traceInterpolation
    (A : Set LoopCircle) (hA : IsClosed A)
    (q : LoopCircle → ℝ) (s : ℝ → LoopCircle)
    (hq : ContinuousOn q A) (hs : ContinuousOn s (Icc (0 : ℝ) 1))
    (hqA : MapsTo q A (Icc (0 : ℝ) 1))
    (hsA : MapsTo s (Icc (0 : ℝ) 1) A)
    (hqs : ∀ t ∈ Icc (0 : ℝ) 1, q (s t) = t)
    (hsq : ∀ z ∈ A, s (q z) = z)
    (hfront : ∀ z ∈ frontier A, q z = 0 ∨ q z = 1)
    (E : OpenPartialHomeomorph LoopCircle ℝ) (hconv : Convex ℝ E.target)
    (β : C(LoopCircle, LoopCircle)) (hβ : M65WeakCircleParameter β)
    (hcap : MapsTo β A E.source) :
    ∃ B : C(LoopCircle, LoopCircle), M65WeakCircleParameter B ∧
      ∀ z, B z = traceInterpolation A q s E β z := by
  let V : Set C(LoopCircle, LoopCircle) := {f | MapsTo f A E.source}
  let H : Set C(LoopCircle, LoopCircle) := range (fun h : LoopCircle ≃ₜ LoopCircle =>
    (⟨h, h.continuous⟩ : C(LoopCircle, LoopCircle)))
  let T : C(LoopCircle, LoopCircle) → C(LoopCircle, LoopCircle) := fun f =>
    ContinuousMap.mkD (traceInterpolation A q s E f) β
  have hV : IsOpen V := ContinuousMap.isOpen_setOfPred_mapsTo hA.isCompact E.open_source
  have hTc : ContinuousOn T V := ContinuousMap.continuousOn_mkD_of_uncurry _ β
    (traceInterpolation_joint_continuous A hA q s hq hqA hsA hsq hfront E hconv)
  have hfun (f : C(LoopCircle, LoopCircle)) (hf : f ∈ V) :
      Continuous (traceInterpolation A q s E f) := by
    have hh := traceInterpolation_joint_continuous A hA q s hq hqA hsA hsq hfront E hconv
    exact hh.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hf, mem_univ _⟩)
  have himage : T β ∈ closure (T '' (H ∩ V)) := by
    apply mem_closure_image ((hTc β hcap).continuousAt (hV.mem_nhds hcap))
    exact (mem_closure_iff_nhds.mpr (by
      intro U hU
      obtain ⟨f, hfU, hfH⟩ := mem_closure_iff_nhds.mp hβ _ (inter_mem hU (hV.mem_nhds hcap))
      exact ⟨f, hfU.1, hfH, hfU.2⟩))
  have hsub : T '' (H ∩ V) ⊆ H := by
    rintro _ ⟨f, ⟨⟨h, rfl⟩, hfV⟩, rfl⟩
    obtain ⟨h', hh'⟩ := traceInterpolation_homeomorph A hA q s hq hs hqA hsA hqs hsq
      hfront E hconv h hfV
    refine ⟨h', ?_⟩
    apply ContinuousMap.ext
    intro z
    change h' z = ContinuousMap.mkD (traceInterpolation A q s E h) β z
    have hhc : Continuous (traceInterpolation A q s E h) := by
      simpa only [ContinuousMap.coe_mk] using hfun ⟨h, h.continuous⟩ hfV
    rw [ContinuousMap.mkD_of_continuous hhc]
    exact hh' z
  refine ⟨T β, (closure_mono hsub) himage, ?_⟩
  intro z
  change ContinuousMap.mkD (traceInterpolation A q s E β) β z = _
  rw [ContinuousMap.mkD_of_continuous (hfun β hcap)]
  rfl

end PoincareConjecture.M65Boundary
