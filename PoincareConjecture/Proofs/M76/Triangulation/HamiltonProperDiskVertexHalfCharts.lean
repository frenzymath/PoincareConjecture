import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexIncidence
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFrontierStars
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalBlockExtension

set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

omit [FiniteDimensional ℝ E] in

theorem HamiltonProperDiskTriangulation.exists_vertex_half_chart
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (w : ℝ) (hw : w ≠ 0) :
    ∃ (boundary : Bool) (g : E → V),
      (T.vertexBlock p).AffineOnFaces g ∧ InjOn g (T.vertexBlock p).space ∧
      g p = 0 ∧ (0 : V) ∈ interior (g '' (T.vertexBlock p).space) ∧
      (∀ x, (g x).2 = w * ((T.pairChart p).chart x).2) ∧
      (∀ x ∈ (T.vertexBlock p).space,
        x ∈ R ↔ (boundary = true → 0 ≤ (g x).1.1)) ∧
      (∀ x ∈ (T.vertexBlock p).space,
        x ∈ D ↔ (boundary = true → 0 ≤ (g x).1.1) ∧ (g x).2 = 0) ∧
      ∀ x ∈ (T.vertexBlock p).space,
        x ∈ frontier R ↔ boundary = true ∧ (g x).1.1 = 0 := by
  classical
  let N := T.vertexBlock p
  let H := (T.pairChart p).chart
  obtain ⟨_, hpN, _, hNS, f, hf, hfi, hfp, hint, hform⟩ :=
    T.vertexBlock_centered_chart p
  have hpH : (p : E) ∈ H.source := hNS (N.vertices_subset_space hpN)
  have hpD : (p : E) ∈ D := T.disk_space.subset
    (T.disk.vertices_subset_space p.property)
  have hpzero : (H p).2 = 0 := by
    rcases (T.pairChart p).model with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact (hd p hpH).mp hpD
    · exact ((hd p hpH).mp hpD).2
  let S : V ≃L[ℝ] V :=
    ((LinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr
      (LinearEquiv.smulOfNeZero ℝ ℝ w hw)).toContinuousLinearEquiv
  let g : E → V := fun x => S (f x)
  have hg : N.AffineOnFaces g := hf.postcomp S.toContinuousLinearMap.toContinuousAffineMap
  have hgi : InjOn g N.space := by
    intro x hx y hy he
    exact hfi hx hy (S.injective he)
  have hgp : g p = 0 := by simp only [g, hfp, map_zero]
  have hgint : (0 : V) ∈ interior (g '' N.space) := by
    have hopen : IsOpen (S '' interior (f '' N.space)) :=
      S.toHomeomorph.isOpenMap _ isOpen_interior
    have hsub : S '' interior (f '' N.space) ⊆ g '' N.space := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := interior_subset hz
      exact ⟨x, hx, rfl⟩
    exact interior_maximal hsub hopen ⟨0, hint, S.map_zero⟩
  have hnormal (x : E) : (g x).2 = w * (H x).2 := by
    change w * (f x).2 = w * (H x).2
    rw [hform]
    change w * ((H x).2 - (H p).2) = w * (H x).2
    rw [hpzero, sub_zero]
  have hnormal0 (x : E) : (g x).2 = 0 ↔ (H x).2 = 0 := by
    rw [hnormal]
    exact mul_eq_zero.trans (or_iff_right hw)
  have hfirst (x : E) : (g x).1.1 = (H x).1.1 - (H p).1.1 := by
    change (f x).1.1 = _
    rw [hform]
    rfl
  by_cases hpF : (p : E) ∈ frontier R
  · have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
      rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hhalf, _⟩
      · exact False.elim (hpF.2 (hinside hpH))
      · exact hhalf
    have hdisk : ∀ x ∈ H.source, x ∈ D ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0 := by
      rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨_, hdisk⟩
      · exact False.elim (hpF.2 (hinside hpH))
      · exact hdisk
    let ell : V →L[ℝ] ℝ :=
      { toFun := fun z => z.1.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := by fun_prop }
    have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
      intro he
      have h := congrArg (fun m : V →ₗ[ℝ] ℝ => m ((1, 0), 0)) he
      change (1 : ℝ) = 0 at h
      exact one_ne_zero h
    have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
    have hpfirst : (H p).1.1 = 0 := (hfront.apply_mem_iff hpH).mpr hpF
    have hfirst' (x : E) : (g x).1.1 = (H x).1.1 := by
      rw [hfirst, hpfirst, sub_zero]
    refine ⟨true, g, hg, hgi, hgp, hgint, hnormal, ?_, ?_, ?_⟩
    · intro x hx
      simpa only [true_implies, hfirst'] using hhalf x (hNS hx)
    · intro x hx
      simpa only [true_implies, hfirst', hnormal0] using hdisk x (hNS hx)
    · intro x hx
      have h := (hfront.apply_mem_iff (hNS hx)).symm
      change x ∈ frontier R ↔ (H x).1.1 = 0 at h
      simpa only [true_and, hfirst'] using h
  · have hNint : N.space ⊆ interior R := T.vertexBlock_subset_interior p hpF
    have hNR : N.space ⊆ R := hNint.trans interior_subset
    have hDnormal (x : E) (hx : x ∈ N.space) : x ∈ D ↔ (H x).2 = 0 := by
      rcases (T.pairChart p).model with ⟨_, hd⟩ | ⟨hr, hd⟩
      · exact hd x (hNS hx)
      · have hR := (hr x (hNS hx)).mp (hNR hx)
        simpa only [hR, true_and] using hd x (hNS hx)
    refine ⟨false, g, hg, hgi, hgp, hgint, hnormal, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Bool.false_eq_true, false_implies, iff_true]
      exact hNR hx
    · intro x hx
      simpa only [Bool.false_eq_true, false_implies, true_and, hnormal0]
        using hDnormal x hx
    · intro x hx
      simp only [Bool.false_eq_true, false_and, iff_false]
      exact fun hF => hF.2 (hNint hx)

end PoincareConjecture.M76.HamiltonIndexOne
