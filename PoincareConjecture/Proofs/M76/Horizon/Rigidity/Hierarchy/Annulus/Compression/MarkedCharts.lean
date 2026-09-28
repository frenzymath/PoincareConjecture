import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem marked_surface_charts_after_interior_change
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N B S S' U A : Set X}
    (hN : PLDomain e N) (hB : IsClosed B) (hU : IsClosed U)
    (hfront : frontier N = (N ∩ B) ∪ (S' ∪ U))
    (hdis : Disjoint S' U) (hA : IsClosed A) (hAB : Disjoint A B)
    (hfixed : ∀ x ∉ A, x ∈ S' ↔ x ∈ S)
    (hboundary : ∀ x ∈ S ∩ B,
      ∃ (T : OpenPartialHomeomorph X V3) (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
        x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
        (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
        ∀ y ∈ T.source, y ∈ B ↔ psi (T y) = 0) :
    ∀ x ∈ S', ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S' ↔ ell (T y) = 0) ∧ Disjoint T.source B) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S' ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ B ↔ psi (T y) = 0) := by
  intro x hx
  by_cases hxB : x ∈ B
  · have hxA : x ∉ A := fun hxA => disjoint_left.mp hAB hxA hxB
    obtain ⟨T, ell, psi, u, v, hxT, hcompat, hu, hv, huv, hS, hmark⟩ :=
      hboundary x ⟨(hfixed x hxA).mp hx, hxB⟩
    refine ⟨T.restrOpen Aᶜ hA.isOpen_compl, ⟨hxT, hxA⟩,
      fun i => (e i).piecewiseAffine_compatible_restrOpen_right T (hcompat i) hA.isOpen_compl,
      Or.inr ⟨ell, psi, u, v, hu, hv, huv, ?_, ?_⟩⟩
    · intro y hy
      exact (hfixed y hy.2).trans (hS y hy.1)
    · exact fun y hy => hmark y hy.1
  · have hxfront : x ∈ frontier N := hfront.symm.subset (Or.inr (Or.inl hx))
    obtain ⟨ell, v, T, hv, hxT, _, hcompat, hhalf⟩ := hN.halfspace x hxfront
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro heq
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [heq, LinearMap.zero_apply] at hval
      exact zero_ne_one hval
    have hplane := T.isImage_frontier_of_affine_nonneg ell hell hhalf
    let V := Bᶜ ∩ Uᶜ
    have hV : IsOpen V := hB.isOpen_compl.inter hU.isOpen_compl
    have hxU : x ∉ U := fun hxU => disjoint_left.mp hdis hx hxU
    refine ⟨T.restrOpen V hV, ⟨hxT, hxB, hxU⟩,
      fun i => (e i).piecewiseAffine_compatible_restrOpen_right T (hcompat i) hV,
      Or.inl ⟨ell, v, hv, ?_, ?_⟩⟩
    · intro y hy
      have hfrontier : y ∈ S' ↔ y ∈ frontier N := by
        rw [hfront]
        have hyB : y ∉ B := hy.2.1
        have hyU : y ∉ U := hy.2.2
        simp only [mem_union, mem_inter_iff, hyB, hyU, and_false, false_or, or_false]
      exact hfrontier.trans (hplane.apply_mem_iff hy.1).symm
    · exact disjoint_left.mpr (fun y hy hyB => hy.2.1 hyB)

end PoincareConjecture.M76
