import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalBlockExtension

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

theorem exists_vertex_half_chart (p : (T.marked 2).vertices)
    (w : ℝ) (hw : w ≠ 0) :
    ∃ (boundary : Bool) (g : (T.index → ℝ × V3) → C3),
      (T.vertexBlock p).AffineOnFaces g ∧ InjOn g (T.vertexBlock p).space ∧
      g p = 0 ∧ (0 : C3) ∈ interior (g '' (T.vertexBlock p).space) ∧
      (∀ x, (g x).2 = w * (T.chart (T.chart_index p) (T.inverse x)).2) ∧
      (∀ x ∈ (T.vertexBlock p).space,
        x ∈ (T.marked 0).space ↔ (boundary = true → 0 ≤ (g x).1.1)) ∧
      (∀ x ∈ (T.vertexBlock p).space,
        x ∈ (T.marked 2).space ↔
          (boundary = true → 0 ≤ (g x).1.1) ∧ (g x).2 = 0) ∧
      ∀ x ∈ (T.vertexBlock p).space,
        x ∈ (T.marked 1).space ↔ boundary = true ∧ (g x).1.1 = 0 := by
  classical
  let N := T.vertexBlock p
  let H := T.chart (T.chart_index p)
  obtain ⟨_, hpN, _, hNS, f, hf, hfi, hfp, hint, hform⟩ :=
    T.vertexBlock_centered_chart p
  have hpH : (T.inverse p : X) ∈ H.source := hNS (N.vertices_subset_space hpN)
  have hpK : (p : T.index → ℝ × V3) ∈ T.ambient.space :=
    T.vertexBlock_subset_ambient p (N.vertices_subset_space hpN)
  have hpD : (T.inverse p : X) ∈ j '' closedBall (0 : V2) 1 :=
    (T.inverse_mem_disk_iff hpK).mpr ((T.marked 2).vertices_subset_space p.property)
  have hpzero : (H (T.inverse p)).2 = 0 := by
    rcases T.chart_model (T.chart_index p) with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact (hd _ hpH).mp hpD
    · exact ((hd _ hpH).mp hpD).2
  let S : C3 ≃L[ℝ] C3 :=
    ((LinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr
      (LinearEquiv.smulOfNeZero ℝ ℝ w hw)).toContinuousLinearEquiv
  let g : (T.index → ℝ × V3) → C3 := fun x => S (f x)
  have hg : N.AffineOnFaces g := hf.postcomp S.toContinuousLinearMap.toContinuousAffineMap
  have hgi : InjOn g N.space := by
    intro x hx y hy he
    exact hfi hx hy (S.injective he)
  have hgp : g p = 0 := by simp only [g, hfp, map_zero]
  have hgint : (0 : C3) ∈ interior (g '' N.space) := by
    have hopen : IsOpen (S '' interior (f '' N.space)) :=
      S.toHomeomorph.isOpenMap _ isOpen_interior
    have hsub : S '' interior (f '' N.space) ⊆ g '' N.space := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := interior_subset hz
      exact ⟨x, hx, rfl⟩
    exact interior_maximal hsub hopen ⟨0, hint, S.map_zero⟩
  have hnormal (x : T.index → ℝ × V3) : (g x).2 = w * (H (T.inverse x)).2 := by
    change w * (f x).2 = w * (H (T.inverse x)).2
    rw [hform]
    change w * ((H (T.inverse x)).2 - (H (T.inverse p)).2) = w * (H (T.inverse x)).2
    rw [hpzero, sub_zero]
  have hnormal0 (x : T.index → ℝ × V3) : (g x).2 = 0 ↔ (H (T.inverse x)).2 = 0 := by
    rw [hnormal]
    exact mul_eq_zero.trans (or_iff_right hw)
  have hfirst (x : T.index → ℝ × V3) :
      (g x).1.1 = (H (T.inverse x)).1.1 - (H (T.inverse p)).1.1 := by
    change (f x).1.1 = _
    rw [hform]
    rfl
  by_cases hpF : (T.inverse p : X) ∈ frontier R
  · have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
      rcases T.chart_model (T.chart_index p) with ⟨hinside, _⟩ | ⟨hhalf, _⟩
      · exact False.elim (hpF.2 (hinside hpH))
      · exact hhalf
    have hdisk : ∀ x ∈ H.source,
        x ∈ j '' closedBall (0 : V2) 1 ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0 := by
      rcases T.chart_model (T.chart_index p) with ⟨hinside, _⟩ | ⟨_, hdisk⟩
      · exact False.elim (hpF.2 (hinside hpH))
      · exact hdisk
    let ell : C3 →L[ℝ] ℝ :=
      { toFun := fun z => z.1.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := by fun_prop }
    have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
      intro he
      have h := congrArg (fun m : C3 →ₗ[ℝ] ℝ => m ((1, 0), 0)) he
      change (1 : ℝ) = 0 at h
      exact one_ne_zero h
    have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
    have hpfirst : (H (T.inverse p)).1.1 = 0 := (hfront.apply_mem_iff hpH).mpr hpF
    have hfirst' (x : T.index → ℝ × V3) : (g x).1.1 = (H (T.inverse x)).1.1 := by
      rw [hfirst, hpfirst, sub_zero]
    refine ⟨true, g, hg, hgi, hgp, hgint, hnormal, ?_, ?_, ?_⟩
    · intro x hx
      have h := (T.inverse_mem_region_iff (T.vertexBlock_subset_ambient p hx)).symm.trans
        (hhalf _ (hNS hx))
      simpa only [true_implies, hfirst'] using h
    · intro x hx
      have h := (T.inverse_mem_disk_iff (T.vertexBlock_subset_ambient p hx)).symm.trans
        (hdisk _ (hNS hx))
      simpa only [true_implies, hfirst', hnormal0] using h
    · intro x hx
      have h := (T.inverse_mem_boundary_iff (T.vertexBlock_subset_ambient p hx)).symm.trans
        (hfront.apply_mem_iff (hNS hx)).symm
      change x ∈ (T.marked 1).space ↔ (H (T.inverse x)).1.1 = 0 at h
      simpa only [true_and, hfirst'] using h
  · have hNint := T.vertexBlock_subset_original_interior p hpF
    have hNR (x : T.index → ℝ × V3) (hx : x ∈ N.space) : (T.inverse x : X) ∈ R :=
      interior_subset (hNint hx)
    have hDnormal (x : T.index → ℝ × V3) (hx : x ∈ N.space) :
        x ∈ (T.marked 2).space ↔ (H (T.inverse x)).2 = 0 := by
      rw [← T.inverse_mem_disk_iff (T.vertexBlock_subset_ambient p hx)]
      rcases T.chart_model (T.chart_index p) with ⟨_, hd⟩ | ⟨hr, hd⟩
      · exact hd _ (hNS hx)
      · have hR := (hr _ (hNS hx)).mp (hNR x hx)
        simpa only [hR, true_and] using hd _ (hNS hx)
    refine ⟨false, g, hg, hgi, hgp, hgint, hnormal, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Bool.false_eq_true, false_implies, iff_true]
      exact (T.inverse_mem_region_iff (T.vertexBlock_subset_ambient p hx)).mp (hNR x hx)
    · intro x hx
      simpa only [Bool.false_eq_true, false_implies, true_and, hnormal0] using hDnormal x hx
    · intro x hx
      simp only [Bool.false_eq_true, false_and, iff_false]
      intro hxB
      exact ((T.inverse_mem_boundary_iff (T.vertexBlock_subset_ambient p hx)).mpr hxB).2
        (hNint hx)

end PoincareConjecture.M76.OriginalProperDiskTriangulation
