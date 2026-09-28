import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Topology.Algebra.Module.Equiv











set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private instance sphereDimensionFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private noncomputable def planeProductCoordinates : E2 ≃L[ℝ] (ℝ × ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)



noncomputable def spherePlaneChart (p : UnitTwoSphere) :
    OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ) :=
  (stereographic' 2 p).trans planeProductCoordinates.toHomeomorph.toOpenPartialHomeomorph


@[simp] theorem spherePlaneChart_source (p : UnitTwoSphere) :
    (spherePlaneChart p).source = {p}ᶜ := by
  simp [spherePlaneChart]



@[simp] theorem spherePlaneChart_target (p : UnitTwoSphere) :
    (spherePlaneChart p).target = univ := by
  simp [spherePlaneChart]



theorem contMDiffOn_spherePlaneChart (p : UnitTwoSphere) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (spherePlaneChart p)
      (spherePlaneChart p).source := by
  have heq : chartAt E2 (-p) = stereographic' 2 p := by
    change stereographic' 2 (- -p) = stereographic' 2 p
    rw [neg_neg]
  have hS : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (stereographic' 2 p)
      (stereographic' 2 p).source := by
    rw [← heq]
    exact contMDiffOn_chart
  simpa [spherePlaneChart] using
    planeProductCoordinates.contDiff.contMDiff.comp_contMDiffOn hS



theorem contMDiff_spherePlaneChart_symm (p : UnitTwoSphere) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (spherePlaneChart p).symm := by
  have heq : chartAt E2 (-p) = stereographic' 2 p := by
    change stereographic' 2 (- -p) = stereographic' 2 p
    rw [neg_neg]
  have hS : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (chartAt E2 (-p)).symm
      (chartAt E2 (-p)).target := contMDiffOn_chart_symm
  rw [heq, stereographic'_target] at hS
  have hI := contMDiffOn_univ.mp hS
  simpa [spherePlaneChart] using
    hI.comp planeProductCoordinates.symm.contDiff.contMDiff




theorem exists_compact_planar_representative (p : UnitTwoSphere)
    (g : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {U : Set UnitTwoSphere} (hU : IsOpen U) (hp : p ∈ U)
    (hfix : ∀ x ∈ U, g x = x) :
    ∃ (h : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) (K : Set (ℝ × ℝ)), IsCompact K ∧
      (∀ y, h y = spherePlaneChart p (g ((spherePlaneChart p).symm y))) ∧
      (∀ y, h.symm y = spherePlaneChart p (g.symm ((spherePlaneChart p).symm y))) ∧
      (∀ y, y ∉ K → h y = y ∧ h.symm y = y) ∧
      (∀ x, x ≠ p → (spherePlaneChart p).symm (h (spherePlaneChart p x)) = g x) := by
  classical
  let T := spherePlaneChart p
  have ht : T.target = univ := spherePlaneChart_target p
  have hs : T.source = {p}ᶜ := spherePlaneChart_source p
  have htarget (y : ℝ × ℝ) : y ∈ T.target := ht ▸ mem_univ y
  have hg : g p = p := hfix p hp
  have hgI : g.symm p = p := by
    have h := congrArg g.symm hg
    simpa only [g.symm_apply_apply] using h.symm
  have hpreserve (f : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
      (hf : f p = p) : MapsTo f T.source T.source := by
    intro x hx
    simp only [hs, mem_compl_iff, mem_singleton_iff] at hx ⊢
    intro heq
    exact hx (f.injective (heq.trans hf.symm))
  have hgsource := hpreserve g hg
  have hgisource := hpreserve g.symm hgI
  let C : (UnitTwoSphere → UnitTwoSphere) → (ℝ × ℝ) → (ℝ × ℝ) :=
    fun f y => T (f (T.symm y))
  have hCleft (f k : UnitTwoSphere → UnitTwoSphere)
      (hf : MapsTo f T.source T.source) (hkf : LeftInverse k f) :
      LeftInverse (C k) (C f) := by
    intro y
    change T (k (T.symm (T (f (T.symm y))))) = y
    rw [T.left_inv (hf (T.map_target (htarget y))), hkf, T.right_inv (htarget y)]
  have hCsmooth (f : UnitTwoSphere → UnitTwoSphere)
      (hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f) (hsf : MapsTo f T.source T.source) :
      ContDiff ℝ ∞ (C f) := by
    apply ContMDiff.contDiff
    intro y
    have hinner := hf.contMDiffAt.comp y (contMDiff_spherePlaneChart_symm p y)
    have houter := (contMDiffOn_spherePlaneChart p).contMDiffAt
      (T.open_source.mem_nhds (hsf (T.map_target (htarget y))))
    exact houter.comp y hinner
  let h : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) :=
    { toEquiv :=
        { toFun := C g
          invFun := C g.symm
          left_inv := hCleft g g.symm hgsource g.symm_apply_apply
          right_inv := hCleft g.symm g hgisource g.apply_symm_apply }
      contMDiff_toFun := (hCsmooth g g.contMDiff hgsource).contMDiff
      contMDiff_invFun := (hCsmooth g.symm g.symm.contMDiff hgisource).contMDiff }
  let K := T '' Uᶜ
  have hsub : Uᶜ ⊆ T.source := by
    intro x hx
    simp only [hs, mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hx hp
  have hK : IsCompact K :=
    hU.isClosed_compl.isCompact.image_of_continuousOn (T.continuousOn.mono hsub)
  have hfixh (y : ℝ × ℝ) (hy : y ∉ K) : h y = y := by
    have hmem : T.symm y ∈ U := by
      by_contra hn
      exact hy ⟨T.symm y, hn, T.right_inv (htarget y)⟩
    change T (g (T.symm y)) = y
    rw [hfix _ hmem, T.right_inv (htarget y)]
  refine ⟨h, K, hK, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro y hy
    refine ⟨hfixh y hy, ?_⟩
    have heq := congrArg h.symm (hfixh y hy)
    simpa only [h.symm_apply_apply] using heq.symm
  · intro x hx
    have hxs : x ∈ T.source := by simpa only [hs, mem_compl_iff, mem_singleton_iff]
    change T.symm (T (g (T.symm (T x)))) = g x
    rw [T.left_inv hxs, T.left_inv (hgsource hxs)]

end PoincareConjecture.M25.Topology3D
