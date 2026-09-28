import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.Blocks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalBlockExtension



set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem exists_vertex_half_chart (p : (T.marked 2).vertices) (w : ℝ) (hw : w ≠ 0) :
    ∃ (boundary : Bool) (g : E → C3),
      (T.vertexBlock p).AffineOnFaces g ∧ InjOn g (T.vertexBlock p).space ∧
      g p = 0 ∧ (0 : C3) ∈ interior (g '' (T.vertexBlock p).space) ∧
      (∀ x, (g x).2 = w * T.height p x) ∧
      (∀ x ∈ (T.vertexBlock p).space,
        x ∈ (T.marked 0).space ↔ (boundary = true → 0 ≤ (g x).1.1)) ∧
      (∀ x ∈ (T.vertexBlock p).space,
        x ∈ (T.marked 2).space ↔
          (boundary = true → 0 ≤ (g x).1.1) ∧ (g x).2 = 0) ∧
      ∀ x ∈ (T.vertexBlock p).space,
        x ∈ (T.marked 1).space ↔ boundary = true ∧ (g x).1.1 = 0 := by
  classical
  let N := T.vertexBlock p
  obtain ⟨_, hpN, _, hf, hfi, hint⟩ := T.vertexBlock_chart p
  have hNS := T.vertexBlock_subset_star p
  have hpS := hNS (N.vertices_subset_space hpN)
  have hpzero : (T.chart p p).2 = 0 :=
    ((T.surface_eq p p hpS).mp ((T.marked 2).vertices_subset_space p.property)).2
  let A : C3 →ᴬ[ℝ] C3 := ContinuousAffineMap.id ℝ C3 -
    ContinuousAffineMap.const ℝ C3 (T.chart p p)
  let S : C3 ≃L[ℝ] C3 :=
    ((LinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr
      (LinearEquiv.smulOfNeZero ℝ ℝ w hw)).toContinuousLinearEquiv
  let g : E → C3 := fun x => S (A (T.chart p x))
  have hg : N.AffineOnFaces g :=
    (hf.postcomp A).postcomp S.toContinuousLinearMap.toContinuousAffineMap
  have hgi : InjOn g N.space := by
    intro x hx y hy he
    exact hfi hx hy (sub_left_inj.mp (S.injective he))
  have hgp : g p = 0 := by
    change S (T.chart p p - T.chart p p) = 0
    rw [sub_self, map_zero]
  let H : C3 ≃ₜ C3 :=
    (ContinuousAffineEquiv.constVAdd ℝ C3 (-T.chart p p)).toHomeomorph.trans S.toHomeomorph
  have hH (x : C3) : H x = S (A x) := by
    change S (-T.chart p p + x) = S (x - T.chart p p)
    rw [sub_eq_add_neg, add_comm]
  have hgint : (0 : C3) ∈ interior (g '' N.space) := by
    have hopen := H.isOpenMap _ (isOpen_interior (s := T.chart p '' N.space))
    have hsub : H '' interior (T.chart p '' N.space) ⊆ g '' N.space := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := interior_subset hz
      exact ⟨x, hx, (hH _).symm⟩
    apply interior_maximal hsub hopen
    exact ⟨T.chart p p, hint, (hH _).trans hgp⟩
  have hn (x : E) : (g x).2 = w * T.height p x := by
    change w * ((T.chart p x).2 - (T.chart p p).2) = w * (T.chart p x).2
    rw [hpzero, sub_zero]
  have hn0 (x : E) : (g x).2 = 0 ↔ T.height p x = 0 := by
    rw [hn, mul_eq_zero, or_iff_right hw]
  have hfirst (x : E) : (g x).1.1 = (T.chart p x).1.1 - (T.chart p p).1.1 := rfl
  by_cases hpB : (p : E) ∈ (T.marked 1).space
  · have hb := T.chart_model p
    rcases hb with hb | hb
    · exact (disjoint_left.mp hb.2 hpS hpB).elim
    have hpfirst := (hb.2 p hpS).mp hpB
    have hfirst' (x : E) : (g x).1.1 = (T.chart p x).1.1 := by
      rw [hfirst, hpfirst, sub_zero]
    refine ⟨true, g, hg, hgi, hgp, hgint, hn, ?_, ?_, ?_⟩
    · intro x hx
      simpa only [true_implies, hfirst'] using hb.1 x (hNS hx)
    · intro x hx
      rw [T.surface_eq p x (hNS hx), hb.1 x (hNS hx)]
      simp only [true_implies, hfirst', hn0]
      rfl
    · intro x hx
      simpa only [true_and, hfirst'] using hb.2 x (hNS hx)
  · have hpface : {(p : E)} ∈ (T.marked 2).faces := p.property
    have hpnot : {(p : E)} ∉ (T.marked 1).faces :=
      fun h => hpB ((T.marked 1).vertices_subset_space h)
    have hNR : N.space ⊆ (T.marked 0).space :=
      T.nonboundary_dual_subset_region hpface hpnot
    have hNB : N.space ∩ (T.marked 1).space = ∅ :=
      T.nonboundary_dual_inter_boundary hpface hpnot
    refine ⟨false, g, hg, hgi, hgp, hgint, hn, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Bool.false_eq_true, false_implies, iff_true]
      exact hNR hx
    · intro x hx
      simp only [Bool.false_eq_true, false_implies, true_and, hn0]
      exact (T.height_eq_zero_iff p (hNS hx) (hNR hx)).symm
    · intro x hx
      simp only [Bool.false_eq_true, false_and, iff_false]
      exact fun h => hNB.subset ⟨hx, h⟩

end Geometry.SimplicialComplex.CoorientedSurfaceStars
