import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Topology.SeparatedMap

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_injective_region_chart
    {X Y ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {p : X → Y} (hp : IsLocallyInjective p)
    {x : X} (hxR : x ∈ R) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ Q : OpenPartialHomeomorph X V3,
      x ∈ Q.source ∧ Q.source ⊆ U ∧ InjOn p Q.source ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (Q.source ⊆ interior R ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ell (Q x) = 0 ∧
          (∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y)) ∧
          ∀ y ∈ Q.source, y ∈ frontier R ↔ ell (Q y) = 0) := by
  obtain ⟨V, hV, hxV, hpV⟩ := hp x
  have hrestrict (B : OpenPartialHomeomorph X V3)
      (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
      (W : Set X) (hW : IsOpen W) :
      ∀ i, (e i).symm.trans (B.restrOpen W hW) ∈ piecewiseAffineGroupoid V3 := by
    intro i
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hB i)).mono
      ((e i).symm.trans (B.restrOpen W hW)).open_source
      (fun z hz => ⟨hz.1, hz.2.1⟩)
  by_cases hxint : x ∈ interior R
  · obtain ⟨i, hxi⟩ := he.cover x
    let W := U ∩ V ∩ interior R
    have hW : IsOpen W := (hU.inter hV).inter isOpen_interior
    let Q := (e i).restrOpen W hW
    refine ⟨Q, ⟨hxi, ⟨hxU, hxV⟩, hxint⟩,
      (fun y hy => hy.2.1.1), hpV.mono (fun y hy => hy.2.1.2),
      hrestrict (e i) (fun k => he.compatible k i) W hW,
      Or.inl (fun y hy => hy.2.2)⟩
  · have hxfront : x ∈ frontier R := ⟨subset_closure hxR, hxint⟩
    obtain ⟨ell, v, B, hv, hxB, hzero, hB, hhalf⟩ := he.halfspace x hxfront
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h] at hval
      norm_num at hval
    have hfront := B.isImage_frontier_of_affine_nonneg ell hell hhalf
    let W := U ∩ V
    have hW : IsOpen W := hU.inter hV
    let Q := B.restrOpen W hW
    refine ⟨Q, ⟨hxB, hxU, hxV⟩, (fun y hy => hy.2.1),
      hpV.mono (fun y hy => hy.2.2), hrestrict B hB W hW,
      Or.inr ⟨ell, v, hv, hzero, ?_, ?_⟩⟩
    · exact fun y hy => hhalf y hy.1
    · exact fun y hy => (hfront.apply_mem_iff hy.1).symm

end PoincareConjecture.M76
