import PoincareConjecture.Proofs.M76.Mathlib.GeometricCoreAttachment
import PoincareConjecture.Proofs.M76.Mathlib.ConvexCoreDecomposition
import PoincareConjecture.Proofs.M76.Mathlib.SmoothLeafGermGluing










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]






theorem IsSmoothLeafFieldOn.exists_convexCellAttachment
    {P : E → EuclideanSubspace E} {U B : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hB : IsClosed B) (hBU : B ⊆ U)
    (a : F →ᴬ[ℝ] E) (b : (X × Y) ≃L[ℝ] F) (hJ : Function.Injective a.contLinear)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hboundary : (fun x => a (b (x, 0))) '' frontier C ⊆ U)
    (hBC : B ∩ (fun x => a (b (x, 0))) '' C ⊆
      (fun x => a (b (x, 0))) '' frontier C)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ F = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint a.contLinear.range L)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ x ∈ frontier C, (P (a (b (x, 0)))).subspace.IsSecantTransverse A) :
    ∃ W : Set E, IsOpen W ∧ B ∪ (fun x => a (b (x, 0))) '' C ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ y ∈ W, Module.finrank ℝ (R y).subspace + Module.finrank ℝ F = Module.finrank ℝ E) ∧
        R =ᶠ[𝓝ˢ B] P ∧
        ∀ x ∈ C, (R (a (b (x, 0)))).subspace.IsSecantTransverse A := by
  let c : X → E := fun x => a (b (x, 0))
  have hcc : Continuous c := a.continuous.comp
    (b.continuous.comp (continuous_id.prodMk continuous_const))
  have hci : Function.Injective c := by
    intro x y hxy
    exact congrArg Prod.fst (b.injective (a.toAffineMap.linear_injective_iff.mp hJ hxy))
  let V := U ∩ P ⁻¹' {L : EuclideanSubspace E | L.subspace.IsSecantTransverse A}
  have hV : IsOpen V := hP.continuousOn.isOpen_inter_preimage hU (isOpen_isSecantTransverse A)
  have hfrontC : frontier C ⊆ c ⁻¹' V := by
    intro x hx
    exact ⟨hboundary ⟨x, hx, rfl⟩, htrans x hx⟩
  obtain ⟨D, hD, hDc, hDi, hDC, hcollarCompact, hcollar, hinter, hcover⟩ :=
    hC.exists_convex_core_decomposition hc hi (hV.preimage hcc) hfrontC
  have hDC' : D ⊆ C := hDC.trans interior_subset
  have hfrontD : frontier D ⊆ C \ interior D := fun x hx =>
    ⟨hDC' (hD.isClosed.frontier_subset hx), hx.2⟩
  have hfrontDV : c '' frontier D ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcollar (hfrontD hx)
  obtain ⟨N, hN, hDN, Q, hQ, hQdim, hPQ⟩ :=
    (hP.mono (show V ⊆ U from inter_subset_left)).exists_coreAttachment hV a b hJ
      hD hDc hDi hfrontDV (fun x hx => hdim x hx.1) A hdisjoint
      (fun x hx => (hcollar (hfrontD hx)).2)
  let B' := B ∪ c '' (C \ interior D)
  have hB' : IsClosed B' := hB.union (hcollarCompact.image hcc).isClosed
  have hB'U : B' ⊆ U := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact hBU hy
    · exact (hcollar hx).1
  have hBD : Disjoint B (c '' D) := by
    apply disjoint_left.mpr
    rintro _ hyB ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hBC ⟨hyB, ⟨x, hDC' hx, rfl⟩⟩
    have he : z = x := hci hzx
    subst z
    exact hz.2 (hDC hx)
  have hBDinter : B' ∩ c '' D = c '' frontier D := by
    dsimp only [B']
    rw [union_inter_distrib_right, hBD.inter_eq, empty_union, ← image_inter hci, hinter]
  have hBcover : B' ∪ c '' D = B ∪ c '' C := by
    dsimp only [B']
    rw [union_assoc, ← image_union, hcover]
  have hPQ' : P =ᶠ[𝓝ˢ (B' ∩ c '' D)] Q := by
    rw [hBDinter]
    exact hPQ
  obtain ⟨W, hW, hBW, R, hR, hsource, hRP, hRQ⟩ :=
    hP.exists_gluing hQ hU hN hB' (hD.image hcc).isClosed hB'U hDN hPQ'
  refine ⟨W, hW, ?_, R, hR, ?_, ?_, ?_⟩
  · rwa [hBcover] at hBW
  · intro y hy
    rcases hsource y hy with ⟨hyU, hRy⟩ | ⟨hyN, hRy⟩
    · rw [hRy]
      exact hdim y hyU
    · rw [hRy]
      exact (hQdim y hyN).1
  · exact hRP.filter_mono (nhdsSet_mono (show B ⊆ B' from subset_union_left))
  · intro x hx
    by_cases hxD : x ∈ D
    · rw [hRQ.self_of_nhdsSet ⟨x, hxD, rfl⟩]
      exact (hQdim (c x) (hDN ⟨x, hxD, rfl⟩)).2
    · have hxcol : x ∈ C \ interior D := ⟨hx, fun hxi => hxD (interior_subset hxi)⟩
      rw [hRP.self_of_nhdsSet (show c x ∈ B' from Or.inr ⟨x, hxcol, rfl⟩)]
      exact (hcollar hxcol).2

end Geometry.EuclideanSubspace
