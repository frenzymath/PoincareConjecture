import PoincareConjecture.Proofs.M76.Mathlib.SmoothTransverseFrames
import PoincareConjecture.Proofs.M76.Mathlib.ParametricLeafGluing
import PoincareConjecture.Proofs.M76.Mathlib.CompactParameterThickening

set_option autoImplicit false

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsSmoothLeafFieldOn.exists_coreAttachment
    {P : E → EuclideanSubspace E} {U : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (a : F →ᴬ[ℝ] E) (b : (X × Y) ≃L[ℝ] F)
    (hJ : Function.Injective a.contLinear)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hboundary : (fun x => a (b (x, 0))) '' frontier C ⊆ U)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ F = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint a.contLinear.range L)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ x ∈ frontier C, (P (a (b (x, 0)))).subspace.IsSecantTransverse A) :
    ∃ V : Set E, IsOpen V ∧ (fun x => a (b (x, 0))) '' C ⊆ V ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R V ∧
        (∀ y ∈ V, Module.finrank ℝ (R y).subspace + Module.finrank ℝ F =
          Module.finrank ℝ E ∧ (R y).subspace.IsSecantTransverse A) ∧
        P =ᶠ[𝓝ˢ ((fun x => a (b (x, 0))) '' frontier C)] R := by
  let c : X → E := fun x => a (b (x, 0))
  let S := c '' frontier C
  obtain ⟨V, hV, hSV, _, G, hG, hspec, hleaf⟩ :=
    hP.exists_transverse_frame_neighborhood hU hboundary a.contLinear hJ hdim A hdisjoint
      (by rintro _ ⟨x, hx, rfl⟩; exact htrans x hx)
  have hfront : IsCompact (frontier C) :=
    hC.of_isClosed_subset isClosed_frontier hC.isClosed.frontier_subset
  obtain ⟨r, hr, hthick⟩ :=
    (a.continuous.comp b.continuous).exists_pos_closedBall_thickening hfront hV
      (fun x hx => hSV ⟨x, hx, rfl⟩)
  have hsmall : ({0} : Set Y) ⊆ interior (Metric.closedBall (0 : Y) r) := by
    apply singleton_subset_iff.mpr
    exact mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds (0 : Y) hr)
  obtain ⟨Q0⟩ : Nonempty {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A} := inferInstance
  obtain ⟨W, hW, hCW, q, hq, hqn, hql, hGq⟩ :=
    a.exists_smooth_parametric_leafAttachment b Q0.val Q0.property.1 hC hc hi
      (isCompact_closedBall (0 : Y) r) isCompact_singleton hsmall hV hG
      (fun y hy => (hspec y hy).1) hleaf
      (by rintro _ ⟨z, hz, rfl⟩; exact hthick hz) A
      (fun z hz => (hspec _ (hthick hz)).2.2)
  let R : E → EuclideanSubspace E := fun y => ⟨(q y).ker⟩
  have hqsurj (y : E) (hy : y ∈ W) : Function.Surjective (q y) :=
    fun v => ⟨a.contLinear v, (hqn y hy).1 v⟩
  have hR : IsSmoothLeafFieldOn R W := IsSmoothLeafFieldOn.of_operator hq hqsurj hql
  have hSsub : S ⊆ (a ∘ b) '' (frontier C ×ˢ ({0} : Set Y)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(x, 0), ⟨hx, mem_singleton 0⟩, rfl⟩
  have hGqS : G =ᶠ[𝓝ˢ S] q := hGq.filter_mono (nhdsSet_mono hSsub)
  refine ⟨W, hW, ?_, R, hR, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hCW ⟨(x, 0), ⟨hx, mem_singleton 0⟩, rfl⟩
  · intro y hy
    refine ⟨?_, (hqn y hy).2⟩
    have hdimq := (q y).toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (hqsurj y hy), finrank_top] at hdimq
    change Module.finrank ℝ (q y).ker + Module.finrank ℝ F = Module.finrank ℝ E
    omega
  · filter_upwards [hGqS, hV.mem_nhdsSet.mpr hSV] with y hyq hyV
    apply EuclideanSubspace.ext
    change (P y).subspace = (q y).ker
    rw [← (hspec y hyV).2.1, hyq]

end Geometry.EuclideanSubspace
