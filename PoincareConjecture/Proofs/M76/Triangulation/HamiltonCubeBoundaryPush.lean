import PoincareConjecture.Proofs.M76.Triangulation.HamiltonBoundaryDepthPush
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnitCubePLCollar
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubpolyhedronZeroSet
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import Mathlib.Analysis.Normed.Module.Ball.Pointwise










set_option autoImplicit false

open Set Metric Geometry
open scoped Pointwise

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "B" => closedBall (0 : V3) 1
local notation "S" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) (1 / 8)
local notation "C" => S ×ˢ I
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8 : ℝ) 1
local notation "Q" => closedBall (0 : V3) (7 / 8)

private theorem finitePL_id_inner_cube : FinitePiecewiseAffineOn (id : V3 → V3) Q := by
  let a : V3 →ᴬ[ℝ] V3 :=
    ((7 / 8 : ℝ) • ContinuousLinearMap.id ℝ V3).toContinuousAffineMap
  have ha : Function.Injective a := smul_right_injective V3 (by norm_num : (7 / 8 : ℝ) ≠ 0)
  have hball := (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3 B S).affine_image
    a ha.injOn
  have himage : a '' B = Q := by
    change (7 / 8 : ℝ) • B = Q
    rw [smul_closedBall' (by norm_num : (7 / 8 : ℝ) ≠ 0)]
    norm_num
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  exact (hKs.trans himage) ▸
    (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK




theorem exists_finitePL_cube_push_fixing_subpolyhedron
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJS : J.space ⊆ S) :
    ∃ f : V3 → V3, FinitePiecewiseAffineOn f B ∧ InjOn f B ∧ MapsTo f B B ∧
      EqOn f id J.space ∧ ∀ x ∈ B, f x ∈ S ↔ x ∈ J.space := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3 B S)
  let L := K.frontierSubcomplex B
  have hL : L.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hLs : L.space = S := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs,
      frontier_closedBall _ one_ne_zero]
  obtain ⟨h, hPL, hh⟩ := L.exists_finitePL_subpolyhedron_zero_set J hL hJ
    (hJS.trans hLs.symm.subset) (show (0 : ℝ) < 1 / 8 by norm_num)
  rw [hLs] at hPL hh
  have hbound : MapsTo h S I := fun x hx => (hh x hx).1
  obtain ⟨hqPL, hqi, hqm, hqzero, hqtop, hqfix⟩ :=
    inwardBoundaryDepthMap_properties h hPL hbound
  let q := inwardBoundaryDepthMap h
  obtain ⟨c, hc, _, hcnorm, hc0⟩ := exists_unitCube_inward_finitePL_collar
  have hccopy := hc
  obtain ⟨fc, hfc, hcval⟩ := hccopy
  obtain ⟨g, hg, hgval⟩ := hc.symm
  have hgm : MapsTo g T C := by
    intro x hx
    rw [← hgval ⟨x, hx⟩]
    exact (c.symm ⟨x, hx⟩).property
  have hfcm : MapsTo fc C T := by
    intro p hp
    rw [← hcval ⟨p, hp⟩]
    exact (c ⟨p, hp⟩).property
  have hfg : LeftInvOn fc g T := by
    intro x hx
    rw [← hgval ⟨x, hx⟩, ← hcval, c.apply_symm_apply]
  have hgf : LeftInvOn g fc C := by
    intro p hp
    rw [← hcval ⟨p, hp⟩, ← hgval, c.symm_apply_apply]
  have hgdepth (x : V3) (hx : x ∈ T) : ‖x‖ = 1 - (g x).2 := by
    have hn := hcnorm (c.symm ⟨x, hx⟩)
    rw [c.apply_symm_apply, hgval] at hn
    exact hn
  have hgfirst (x : V3) (hx : x ∈ T) (hz : (g x).2 = 0) : (g x).1 = x := by
    have hv := hc0 ⟨g x, hgm hx⟩ hz
    rw [hcval, hfg hx] at hv
    exact hv.symm
  let F : V3 → V3 := fc ∘ q ∘ g
  have hFPL : FinitePiecewiseAffineOn F T :=
    hfc.comp (hqPL.comp hg hgm) (fun x hx => hqm (hgm hx))
  have hFm : MapsTo F T T := fun x hx => hfcm (hqm (hgm hx))
  have hFi : InjOn F T := by
    intro x hx y hy hxy
    exact hfg.injOn hx hy (hqi (hgf.injOn (hqm (hgm hx)) (hqm (hgm hy)) hxy))
  have hFnorm (x : V3) (hx : x ∈ T) : ‖F x‖ = 1 - (q (g x)).2 := by
    have hn := hcnorm ⟨q (g x), hqm (hgm hx)⟩
    rwa [hcval] at hn
  have hFQ (x : V3) (hx : x ∈ T) (hxQ : x ∈ Q) : F x = x := by
    have ht : (g x).2 = 1 / 8 := by
      have hb := mem_closedBall_zero_iff.mp hxQ
      have hd := hgdepth x hx
      have hl := hx.1
      linarith
    change fc (inwardBoundaryDepthMap h (g x)) = x
    rw [hqtop _ (hgm hx) ht, hfg hx]
  have hST : S ⊆ T := by
    intro x hx
    change 7 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 1
    rw [mem_sphere_zero_iff_norm.mp hx]
    norm_num
  have hFJ (x : V3) (hx : x ∈ J.space) : F x = x := by
    have hxS := hJS hx
    have hxT := hST hxS
    have ht : (g x).2 = 0 := by
      have hd := hgdepth x hxT
      rw [mem_sphere_zero_iff_norm.mp hxS] at hd
      linarith
    have hz : h (g x).1 = 0 := by
      rw [hgfirst x hxT ht]
      exact (hh x hxS).2.mpr hx
    change fc (inwardBoundaryDepthMap h (g x)) = x
    rw [hqfix _ (hgm hxT) hz, hfg hxT]
  have hFS (x : V3) (hx : x ∈ T) : F x ∈ S ↔ x ∈ J.space := by
    constructor
    · intro hxs
      have hn := mem_sphere_zero_iff_norm.mp hxs
      rw [hFnorm x hx] at hn
      have hzero : (q (g x)).2 = 0 := by linarith
      obtain ⟨ht, hhzero⟩ := (hqzero _ (hgm hx)).mp hzero
      have hxS : x ∈ S := by
        apply mem_sphere_zero_iff_norm.mpr
        rw [hgdepth x hx, ht, sub_zero]
      rw [hgfirst x hx ht] at hhzero
      exact (hh x hxS).2.mp hhzero
    · intro hxJ
      rw [hFJ x hxJ]
      exact hJS hxJ
  let f : V3 → V3 := fun x => if x ∈ T then F x else x
  have hfT (x : V3) (hx : x ∈ T) : f x = F x := if_pos hx
  have hfQ (x : V3) (hx : x ∈ Q) : f x = x := by
    by_cases hxT : x ∈ T
    · rw [hfT x hxT, hFQ x hxT hx]
    · exact if_neg hxT
  have hcover : T ∪ Q = B := by
    ext x
    change ((7 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 1) ∨ x ∈ Q) ↔ x ∈ B
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff]
    constructor
    · rintro (hx | hx)
      · exact hx.2
      · linarith
    · intro hx
      by_cases hl : 7 / 8 ≤ ‖x‖
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr (le_of_not_ge hl)
  have hfPL : FinitePiecewiseAffineOn f B := by
    rw [← hcover]
    exact finitePiecewiseAffineOn_union
      (hFPL.congr (fun x hx => (hfT x hx).symm))
      (finitePL_id_inner_cube.congr (fun x hx => (hfQ x hx).symm))
  refine ⟨f, hfPL, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxT : x ∈ T <;> by_cases hyT : y ∈ T
    · rw [hfT x hxT, hfT y hyT] at hxy
      exact hFi hxT hyT hxy
    · have hyval : f y = y := if_neg hyT
      rw [hfT x hxT, hyval] at hxy
      exact False.elim (hyT (hxy ▸ hFm hxT))
    · have hxval : f x = x := if_neg hxT
      rw [hxval, hfT y hyT] at hxy
      exact False.elim (hxT (hxy.symm ▸ hFm hyT))
    · simpa only [f, if_neg hxT, if_neg hyT] using hxy
  · intro x hx
    by_cases hxT : x ∈ T
    · rw [hfT x hxT]
      exact mem_closedBall_zero_iff.mpr (hFm hxT).2
    · simpa only [f, if_neg hxT] using hx
  · intro x hx
    exact (hfT x (hST (hJS hx))).trans (hFJ x hx)
  · intro x hx
    by_cases hxT : x ∈ T
    · rw [hfT x hxT]
      exact hFS x hxT
    · have hxS : x ∉ S := fun h => hxT (hST h)
      have hxJ : x ∉ J.space := fun h => hxS (hJS h)
      simp only [f, if_neg hxT, hxS, hxJ]

end PoincareConjecture.M76
