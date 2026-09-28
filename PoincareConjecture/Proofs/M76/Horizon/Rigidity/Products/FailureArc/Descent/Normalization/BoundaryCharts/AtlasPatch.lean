import PoincareConjecture.Proofs.M76.Rigidity.CompatibleChartPatch
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedPatchImage
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBoundaryLink
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)





theorem exists_original_boundary_source_pair_chart
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → X} (hj : PolyhedralPLInCharts e j K.space)
    (hemb : Topology.IsEmbedding (fun z : K.space => j z))
    (z : K.space) (H : OpenPartialHomeomorph V V2)
    (hzH : (z : V) ∈ H.source) (hHz : H z = 0)
    (hHi : LocallyPiecewiseAffineOn H.symm H.target)
    (B : V2 →ₗ[ℝ] ℝ) (hB : B ≠ 0)
    (hhalf : ∀ x ∈ H.source, x ∈ K.space ↔ 0 ≤ B (H x))
    (G : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3)
    (hzG : j z ∈ G.source) (hGz : G (j z) = 0)
    (A : V3 →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    (hpositive : ∀ x ∈ K.space, j x ∈ G.source → 0 ≤ A (G (j x)))
    (hzero : ∀ x ∈ K.space, x ∈ H.source → j x ∈ G.source →
      (A (G (j x)) = 0 ↔ B (H x) = 0)) :
    ∃ C : OpenPartialHomeomorph X C3,
      j z ∈ C.source ∧ C.source ⊆ G.source ∧
      C.target = interior (CoordinateHalfBoxes.box 1) ∧ C (j z) = 0 ∧
      (∀ x ∈ C.source, 0 ≤ A (G x) ↔ 0 ≤ (C x).1.1) ∧
      (∀ x ∈ C.source, x ∈ j '' K.space ↔ 0 ≤ (C x).1.1 ∧ (C x).2 = 0) ∧
      ∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans C) ((e i).symm.trans C).source ∧
        LocallyPiecewiseAffineOn (C.symm.trans (e i)) (C.symm.trans (e i)).source := by
  classical
  obtain ⟨N, W, hN, hNK, hW, hzW, hWN, hNG, hcoords⟩ :=
    hj.exists_finite_compatible_chart_patch K hK G hcompat z hzG
  have hzN : (z : V) ∈ N.space := hWN ⟨z, hzW, rfl⟩
  obtain ⟨v, T, hT, hNT, hv, hvcoords⟩ := hcoords.exists_locallyPiecewiseAffine_extension
  have hvj (x : V) (hx : x ∈ N.space) : v x = G (j x) := hvcoords hx
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  have hzO : (z : V) ∈ O := by
    change z ∈ (Subtype.val : K.space → V) ⁻¹' O
    rwa [hOW]
  have hON : O ∩ K.space ⊆ N.space := by
    intro x hx
    have hxW : (⟨x, hx.2⟩ : K.space) ∈ W := by rw [← hOW]; exact hx.1
    exact hWN ⟨⟨x, hx.2⟩, hxW, rfl⟩
  let U := H.target ∩ H.symm ⁻¹' (T ∩ O)
  have hU : IsOpen U := H.isOpen_inter_preimage_symm (hT.inter hO)
  have hHinv0 : H.symm 0 = (z : V) :=
    (congrArg H.symm hHz.symm).trans (H.left_inv hzH)
  have h0U : (0 : V2) ∈ U := by
    refine ⟨hHz ▸ H.map_source hzH, ?_⟩
    change H.symm 0 ∈ T ∩ O
    rw [hHinv0]
    exact ⟨hNT hzN, hzO⟩
  let f : V2 → V3 := v ∘ H.symm
  have hflocal : LocallyPiecewiseAffineOn f U :=
    (hv.comp hHi).mono hU (fun x hx => ⟨hx.1, hx.2.1⟩)
  obtain ⟨C0, forms, _, hC0, _, h0C0, hC0U, _, hrep, _, _⟩ :=
    hU.exists_small_convex_halfspace_frontier h0U (ContinuousLinearEquiv.refl ℝ V2)
  let Q := C0 ∩ {x | 0 ≤ B x}
  have hQc : IsCompact Q := hC0.inter_right
    (isClosed_le continuous_const B.continuous_of_finiteDimensional)
  let bounds : Finset (V2 →ᵃ[ℝ] ℝ) := Finset.univ.image
    (fun i => (forms i).toAffineMap - AffineMap.const ℝ V2 1)
  have hbounds : C0 = {x | ∀ a ∈ bounds, a x ≤ 0} := by
    rw [hrep]
    ext x
    simp only [bounds, Finset.mem_image, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff, AffineMap.coe_sub,
      Pi.sub_apply, LinearMap.coe_toAffineMap, AffineMap.const_apply, sub_nonpos]
  have hQrep : Q = {x | ∀ a ∈ insert (-B.toAffineMap) bounds, a x ≤ 0} := by
    ext x
    simp only [Q, mem_inter_iff, hbounds, mem_ofPred_eq, Finset.mem_insert,
      forall_eq_or_imp]
    change ((∀ a ∈ bounds, a x ≤ 0) ∧ 0 ≤ B x) ↔
      (-B x ≤ 0 ∧ ∀ a ∈ bounds, a x ≤ 0)
    rw [neg_nonpos, and_comm]
  obtain ⟨J, hJ, hJQ⟩ := hQc.exists_finite_triangulation_of_halfspaces _ hQrep
  have hQU : Q ⊆ U := fun _ hx => hC0U hx.1
  have hf : FinitePiecewiseAffineOn f Q := by
    rw [← hJQ]
    exact hflocal.finitePiecewiseAffineOn J hJ (hJQ.subset.trans hQU)
  have hqK (x : V2) (hx : x ∈ Q) : H.symm x ∈ K.space := by
    apply (hhalf (H.symm x) (H.map_target (hQU hx).1)).mpr
    rw [H.right_inv (hQU hx).1]
    exact hx.2
  have hqN (x : V2) (hx : x ∈ Q) : H.symm x ∈ N.space :=
    hON ⟨(hQU hx).2.2, hqK x hx⟩
  have hvalue (x : V2) (hx : x ∈ Q) : f x = G (j (H.symm x)) := hvj _ (hqN x hx)
  have hinj : InjOn f Q := by
    intro x hx y hy hxy
    have hjxy : j (H.symm x) = j (H.symm y) :=
      G.injOn (hNG (hqN x hx)) (hNG (hqN y hy))
        ((hvalue x hx).symm.trans (hxy.trans (hvalue y hy)))
    have hxy' : (⟨H.symm x, hqK x hx⟩ : K.space) = ⟨H.symm y, hqK y hy⟩ :=
      hemb.injective hjxy
    have hcoord := congrArg (fun w : K.space => H w) hxy'
    simpa only [H.right_inv (hQU hx).1, H.right_inv (hQU hy).1] using hcoord
  have hf0 : f 0 = 0 := by
    change v (H.symm 0) = 0
    rw [hHinv0, hvj _ hzN, hGz]
  have h0Q : (0 : V2) ∈ Q := ⟨interior_subset h0C0, by simp⟩
  have hfpositive (x : V2) (hx : x ∈ Q) : 0 ≤ A (f x) := by
    rw [hvalue x hx]
    exact hpositive _ (hqK x hx) (hNG (hqN x hx))
  have hfzero (x : V2) (hx : x ∈ Q) : A (f x) = 0 ↔ B x = 0 := by
    rw [hvalue x hx,
      hzero _ (hqK x hx) (H.map_target (hQU hx).1) (hNG (hqN x hx)),
      H.right_inv (hQU hx).1]
  let P := H.symm '' Q
  have hPK : P ⊆ K.space := by rintro _ ⟨x, hx, rfl⟩; exact hqK x hx
  have hPG : MapsTo j P G.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNG (hqN x hx)
  let W' : Set K.space := Subtype.val ⁻¹' (H.source ∩ H ⁻¹' interior C0)
  have hW' : IsOpen W' :=
    (H.isOpen_inter_preimage isOpen_interior).preimage continuous_subtype_val
  have hzW' : z ∈ W' := by
    refine ⟨hzH, ?_⟩
    change H z ∈ interior C0
    rw [hHz]
    exact h0C0
  have hW'P : Subtype.val '' W' ⊆ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨H x, ⟨interior_subset hx.2, (hhalf x hx.1).mp x.property⟩,
      H.left_inv hx.1⟩
  obtain ⟨V, hV, hzV, hVt, hfull⟩ :=
    hemb.exists_open_chart_image_eq_of_patch G hPK hPG z W' hW' hzW' hW'P
  have h0V : (0 : V3) ∈ V := hGz ▸ hzV
  have himage : (G ∘ j) '' P = f '' Q := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, hvalue y hy⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨H.symm y, ⟨y, hy, rfl⟩, (hvalue y hy).symm⟩
  have hfull' : (G '' (j '' K.space ∩ G.source)) ∩ V = (f '' Q) ∩ V := by
    rw [← himage]
    exact hfull
  obtain ⟨C, h0C, hCV, hCt, hC, hCi, hC0', hCA, hCS⟩ :=
    HamiltonIndexOne.exists_pair_chart_of_finitePL_halfplane_patch (by simp)
      hf hinj hf0 h0Q B hB (fun _ hx => hx.2) isOpen_interior h0C0
      (fun _ hx => ⟨fun h => h.2, fun h => ⟨interior_subset hx, h⟩⟩)
      A hA hfpositive hfzero hV h0V hfull'
  let F := G.trans C
  have hzF : j z ∈ F.source := by
    refine ⟨hzG, ?_⟩
    change G (j z) ∈ C.source
    rwa [hGz]
  have hFt : F.target = C.target := by
    apply inter_eq_left.mpr
    exact fun x hx => hVt (hCV (C.map_target hx))
  refine ⟨F, hzF, inter_subset_left, hFt.trans hCt, ?_, ?_, ?_, ?_⟩
  · change C (G (j z)) = 0
    rw [hGz, hC0']
  · intro x hx
    exact hCA (G x) hx.2
  · intro x hx
    have hmem : x ∈ j '' K.space ↔ G x ∈ G '' (j '' K.space ∩ G.source) := by
      constructor
      · intro hjx
        exact ⟨x, ⟨hjx, hx.1⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hyG⟩, hyx⟩
        exact G.injOn hyG hx.1 hyx ▸ hy
    exact hmem.trans (hCS (G x) hx.2)
  · intro i
    have hc := (mem_piecewiseAffineGroupoid_iff V3 _).mp (hcompat i)
    have hforward : LocallyPiecewiseAffineOn (((e i).symm.trans G).trans C)
        (((e i).symm.trans G).trans C).source := hC.comp hc.1
    have hinverse : LocallyPiecewiseAffineOn (C.symm.trans (G.symm.trans (e i)))
        (C.symm.trans (G.symm.trans (e i))).source := hc.2.comp hCi
    constructor
    · simpa only [F, OpenPartialHomeomorph.trans_assoc] using hforward
    · simpa only [F, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hinverse

end PoincareConjecture.M76

