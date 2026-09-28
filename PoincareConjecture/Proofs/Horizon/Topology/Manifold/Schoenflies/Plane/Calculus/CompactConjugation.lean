import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.OpenPartialHomeomorph.Basic











set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace Poincare.Manifold.Schoenflies.Plane



theorem exists_compact_tube_conjugate
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : OpenPartialHomeomorph V W)
    (hT : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (D : V ≃ₘ[ℝ] V) {K : Set V} (hK : IsCompact K) (hKs : K ⊆ T.source)
    (hfix : ∀ x, x ∉ K → D x = x) :
    ∃ A : W ≃ₘ[ℝ] W,
      (∀ x ∈ T.target, A x = T (D (T.symm x))) ∧
      (∀ x ∈ T.target, A.symm x = T (D.symm (T.symm x))) ∧
      (∀ x, x ∉ T '' K → A x = x) ∧
      (∀ x, x ∉ T '' K → A.symm x = x) ∧
      HasCompactSupport (fun x => A x - x) ∧
      HasCompactSupport (fun x => A.symm x - x) := by
  classical
  have hfixInv (x : V) (hx : x ∉ K) : D.symm x = x := by
    have h := congrArg D.symm (hfix x hx)
    simpa only [D.symm_apply_apply] using h.symm
  have hsource (f : V ≃ₘ[ℝ] V) (hf : ∀ x, x ∉ K → f x = x) :
      MapsTo f T.source T.source := by
    intro x hx
    by_contra hn
    have hnK : f x ∉ K := fun h => hn (hKs h)
    have heq : f x = x := f.injective (hf (f x) hnK)
    exact hn (heq.symm ▸ hx)
  have hDsource := hsource D hfix
  have hGsource := hsource D.symm hfixInv
  let C : (V → V) → W → W := fun f x =>
    if x ∈ T.target then T (f (T.symm x)) else x
  have hCapply (f : V → V) (x : W) (hx : x ∈ T.target) :
      C f x = T (f (T.symm x)) := by simp only [C, if_pos hx]
  have hCfix (f : V → V) (hf : ∀ x, x ∉ K → f x = x)
      (x : W) (hx : x ∉ T '' K) : C f x = x := by
    by_cases ht : x ∈ T.target
    · have hnK : T.symm x ∉ K := fun h => hx ⟨T.symm x, h, T.right_inv ht⟩
      rw [hCapply f x ht, hf _ hnK, T.right_inv ht]
    · simp only [C, if_neg ht]
  have hCleft (f g : V → V) (hf : MapsTo f T.source T.source)
      (hgf : LeftInverse g f) : LeftInverse (C g) (C f) := by
    intro x
    by_cases hx : x ∈ T.target
    · have hsf : f (T.symm x) ∈ T.source := hf (T.map_target hx)
      have htarget : C f x ∈ T.target := by
        rw [hCapply f x hx]
        exact T.map_source hsf
      calc
        C g (C f x) = T (g (T.symm (C f x))) := hCapply g _ htarget
        _ = T (g (T.symm (T (f (T.symm x))))) := by rw [hCapply f x hx]
        _ = x := by rw [T.left_inv hsf, hgf, T.right_inv hx]
    · simp only [C, if_neg hx]
  have himage : IsCompact (T '' K) :=
    hK.image_of_continuousOn (T.continuousOn.mono hKs)
  have hCsmooth (f : V → V) (hf : ContDiff ℝ ∞ f)
      (hfsource : MapsTo f T.source T.source) (hffix : ∀ x, x ∉ K → f x = x) :
      ContDiff ℝ ∞ (C f) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ T.target
    · have hi := hInv.contDiffAt (T.open_target.mem_nhds hx)
      have ho := hT.contDiffAt
        (T.open_source.mem_nhds (hfsource (T.map_target hx)))
      apply (ho.comp x (hf.contDiffAt.comp x hi)).congr_of_eventuallyEq
      filter_upwards [T.open_target.mem_nhds hx] with y hy
      exact hCapply f y hy
    · have hn : x ∉ T '' K := by
        rintro ⟨y, hy, rfl⟩
        exact hx (T.map_source (hKs hy))
      apply contDiffAt_id.congr_of_eventuallyEq
      filter_upwards [himage.isClosed.isOpen_compl.mem_nhds hn] with y hy
      exact hCfix f hffix y hy
  let A : W ≃ₘ[ℝ] W :=
    { toEquiv :=
        { toFun := C D
          invFun := C D.symm
          left_inv := hCleft D D.symm hDsource D.symm_apply_apply
          right_inv := hCleft D.symm D hGsource D.apply_symm_apply }
      contMDiff_toFun := (hCsmooth D D.contDiff hDsource hfix).contMDiff
      contMDiff_invFun := (hCsmooth D.symm D.symm.contDiff hGsource hfixInv).contMDiff }
  refine ⟨A, hCapply D, hCapply D.symm, hCfix D hfix, hCfix D.symm hfixInv, ?_, ?_⟩
  · exact HasCompactSupport.intro himage (fun x hx => sub_eq_zero.mpr (hCfix D hfix x hx))
  · exact HasCompactSupport.intro himage
      (fun x hx => sub_eq_zero.mpr (hCfix D.symm hfixInv x hx))

end Poincare.Manifold.Schoenflies.Plane

namespace Poincare.Manifold.Schoenflies




theorem exists_supported_partial_chart_transport
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (c : PartialDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, W) V W ∞)
    (D : V ≃ₘ[ℝ] V) {K : Set V} (hK : IsCompact K) (hKs : K ⊆ c.source)
    (hfix : ∀ x, x ∉ K → D x = x) :
    ∃ G : W ≃ₘ[ℝ] W,
      IsCompact (c '' K) ∧
      (∀ y, y ∉ c '' K → G y = y) ∧
      (∀ y, y ∉ c '' K → G.symm y = y) ∧
      (∀ x ∈ c.source, G (c x) = c (D x)) ∧
      (∀ x ∈ c.source, G.symm (c x) = c (D.symm x)) := by
  obtain ⟨G, hG, hGi, hfixG, hfixGi, _, _⟩ :=
    Plane.exists_compact_tube_conjugate c.toOpenPartialHomeomorph
      c.contMDiffOn.contDiffOn c.symm.contMDiffOn.contDiffOn D hK hKs hfix
  refine ⟨G, hK.image_of_continuousOn
    (c.toOpenPartialHomeomorph.continuousOn.mono hKs), hfixG, hfixGi, ?_, ?_⟩
  · intro x hx
    have h := hG (c x) (c.map_source hx)
    change G (c x) = c (D (c.symm (c x))) at h
    have hi : c.symm (c x) = x := c.left_inv hx
    simpa only [hi] using h
  · intro x hx
    have h := hGi (c x) (c.map_source hx)
    change G.symm (c x) = c (D.symm (c.symm (c x))) at h
    have hi : c.symm (c x) = x := c.left_inv hx
    simpa only [hi] using h

end Poincare.Manifold.Schoenflies
