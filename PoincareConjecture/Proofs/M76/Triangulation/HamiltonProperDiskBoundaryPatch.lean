import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBoundaryLink
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1





theorem exists_boundary_pair_chart_of_actual_disk_charts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) {S : Set E}
    (b : Cube ≃ₜ S) (hb : b.IsFinitePL) (z : Cube)
    (H : OpenPartialHomeomorph V2 V2) (hzH : (z : V2) ∈ H.source)
    (hHz : H z = 0)
    (hHi : LocallyPiecewiseAffineOn H.symm H.target)
    (B : V2 →ₗ[ℝ] ℝ) (hB : B ≠ 0)
    (hhalf : ∀ x ∈ H.source, x ∈ Cube ↔ 0 ≤ B (H x))
    (hboundary : ∀ x ∈ H.source, x ∈ sphere (0 : V2) 1 ↔ B (H x) = 0)
    (G : OpenPartialHomeomorph E E) (hzG : (b z : E) ∈ G.source)
    (hGz : G (b z) = 0)
    (hG : LocallyPiecewiseAffineOn G G.source)
    (hGi : LocallyPiecewiseAffineOn G.symm G.target)
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    (hpositive : ∀ x : Cube, (b x : E) ∈ G.source → 0 ≤ A (G (b x)))
    (hzero : ∀ x : Cube, (b x : E) ∈ G.source →
      (A (G (b x)) = 0 ↔ (x : V2) ∈ sphere (0 : V2) 1)) :
    ∃ K : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ),
      (b z : E) ∈ K.source ∧ K.source ⊆ G.source ∧
      K.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn K K.source ∧
      LocallyPiecewiseAffineOn K.symm K.target ∧ K (b z) = 0 ∧
      (∀ x ∈ K.source, 0 ≤ A (G x) ↔ 0 ≤ (K x).1.1) ∧
      ∀ x ∈ K.source, x ∈ S ↔ 0 ≤ (K x).1.1 ∧ (K x).2 = 0 := by
  classical
  obtain ⟨u, hu, hbu⟩ := hb
  obtain ⟨v, T, hT, hCubeT, hv, hvu⟩ := hu.exists_locallyPiecewiseAffine_extension
  have hvb (x : Cube) : v x = (b x : E) := (hvu x.property).trans (hbu x).symm
  let P := T ∩ v ⁻¹' G.source
  have hP : IsOpen P := hv.continuousOn.isOpen_inter_preimage hT G.open_source
  have hzP : (z : V2) ∈ P := ⟨hCubeT z.property, by
    change v z ∈ G.source
    rw [hvb]
    exact hzG⟩
  let W := H.target ∩ H.symm ⁻¹' P
  have hW : IsOpen W := H.isOpen_inter_preimage_symm hP
  have hHinv0 : H.symm 0 = (z : V2) :=
    (congrArg H.symm hHz.symm).trans (H.left_inv hzH)
  have h0W : (0 : V2) ∈ W := by
    refine ⟨hHz ▸ H.map_source hzH, ?_⟩
    change H.symm 0 ∈ P
    rwa [hHinv0]
  let f : V2 → E := fun x => G (v (H.symm x))
  have hbase : LocallyPiecewiseAffineOn (v ∘ H.symm) W :=
    (hv.mono hP inter_subset_left).comp hHi
  have hflocal : LocallyPiecewiseAffineOn f W :=
    (hG.comp hbase).mono hW (fun x hx => ⟨hx, hx.2.2⟩)
  obtain ⟨C, L, _, hC, _, h0C, hCW, _, hrep, _, _⟩ :=
    hW.exists_small_convex_halfspace_frontier h0W (ContinuousLinearEquiv.refl ℝ V2)
  let Q := C ∩ {x | 0 ≤ B x}
  have hQcompact : IsCompact Q := hC.inter_right
    (isClosed_le continuous_const B.continuous_of_finiteDimensional)
  let forms : Finset (V2 →ᵃ[ℝ] ℝ) := Finset.univ.image
    (fun i => (L i).toAffineMap - AffineMap.const ℝ V2 1)
  have hforms : C = {x | ∀ a ∈ forms, a x ≤ 0} := by
    rw [hrep]
    ext x
    simp only [forms, Finset.mem_image, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff, AffineMap.coe_sub,
      Pi.sub_apply, LinearMap.coe_toAffineMap, AffineMap.const_apply, sub_nonpos]
  have hQrep : Q = {x | ∀ a ∈ insert (-B.toAffineMap) forms, a x ≤ 0} := by
    ext x
    simp only [Q, mem_inter_iff, hforms, mem_ofPred_eq, Finset.mem_insert,
      forall_eq_or_imp]
    change ((∀ a ∈ forms, a x ≤ 0) ∧ 0 ≤ B x) ↔
      (-B x ≤ 0 ∧ ∀ a ∈ forms, a x ≤ 0)
    rw [neg_nonpos, and_comm]
  obtain ⟨J, hJ, hJQ⟩ := hQcompact.exists_finite_triangulation_of_halfspaces _ hQrep
  have hQW : Q ⊆ W := fun _ hx => hCW hx.1
  have hf : FinitePiecewiseAffineOn f Q := by
    rw [← hJQ]
    exact hflocal.finitePiecewiseAffineOn J hJ (hJQ.subset.trans hQW)
  have hinverse (x : V2) (hx : x ∈ Q) : H.symm x ∈ Cube := by
    apply (hhalf (H.symm x) (H.map_target (hQW hx).1)).mpr
    rw [H.right_inv (hQW hx).1]
    exact hx.2
  have hvalue (x : V2) (hx : x ∈ Q) :
      f x = G (b ⟨H.symm x, hinverse x hx⟩) := by
    change G (v (H.symm x)) = _
    rw [hvb ⟨H.symm x, hinverse x hx⟩]
  have htarget (x : V2) (hx : x ∈ Q) :
      (b ⟨H.symm x, hinverse x hx⟩ : E) ∈ G.source := by
    rw [← hvb]
    exact (hQW hx).2.2
  have hinj : InjOn f Q := by
    intro x hx y hy hxy
    have hvxy : v (H.symm x) = v (H.symm y) :=
      G.injOn (hQW hx).2.2 (hQW hy).2.2 hxy
    rw [hvb ⟨H.symm x, hinverse x hx⟩, hvb ⟨H.symm y, hinverse y hy⟩] at hvxy
    have hi := congrArg Subtype.val (b.injective (Subtype.ext hvxy))
    have hh := congrArg H hi
    simpa only [H.right_inv (hQW hx).1, H.right_inv (hQW hy).1] using hh
  have hf0 : f 0 = 0 := by
    change G (v (H.symm 0)) = 0
    rw [hHinv0, hvb z, hGz]
  have h0Q : (0 : V2) ∈ Q := ⟨interior_subset h0C, by
    change 0 ≤ B (0 : V2)
    rw [map_zero]⟩
  have hfpositive (x : V2) (hx : x ∈ Q) : 0 ≤ A (f x) := by
    rw [hvalue x hx]
    exact hpositive _ (htarget x hx)
  have hfzero (x : V2) (hx : x ∈ Q) : A (f x) = 0 ↔ B x = 0 := by
    rw [hvalue x hx, hzero _ (htarget x hx),
      hboundary (H.symm x) (H.map_target (hQW hx).1), H.right_inv (hQW hx).1]
  let O := H.source ∩ H ⁻¹' interior C
  have hO : IsOpen O := H.isOpen_inter_preimage isOpen_interior
  have hzO : (z : V2) ∈ O := ⟨hzH, by
    change H z ∈ interior C
    rw [hHz]
    exact h0C⟩
  let Db : Set S := b.symm ⁻¹' ((Subtype.val : Cube → V2) ⁻¹' O)
  have hDb : IsOpen Db := (hO.preimage continuous_subtype_val).preimage b.symm.continuous
  obtain ⟨V0, hV0, hDbV0⟩ := isOpen_induced_iff.mp hDb
  have hzV0 : (b z : E) ∈ V0 := by
    change b z ∈ (Subtype.val : S → E) ⁻¹' V0
    rw [hDbV0]
    change (b.symm (b z) : V2) ∈ O
    rw [b.symm_apply_apply]
    exact hzO
  let V := G.target ∩ G.symm ⁻¹' V0
  have hV : IsOpen V := G.isOpen_inter_preimage_symm hV0
  have h0V : (0 : E) ∈ V := by
    refine ⟨hGz ▸ G.map_source hzG, ?_⟩
    change G.symm 0 ∈ V0
    rw [← hGz, G.left_inv hzG]
    exact hzV0
  let S' := G '' (S ∩ G.source)
  have hfull : S' ∩ V = (f '' Q) ∩ V := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxV⟩
      have hyV0 : y ∈ V0 := by
        have h := hxV.2
        change G.symm (G y) ∈ V0 at h
        rwa [G.left_inv hy.2] at h
      let t : Cube := b.symm ⟨y, hy.1⟩
      have htO : (t : V2) ∈ O := by
        have ht : (⟨y, hy.1⟩ : S) ∈ (Subtype.val : S → E) ⁻¹' V0 := hyV0
        rwa [hDbV0] at ht
      have htQ : H t ∈ Q := ⟨interior_subset htO.2, (hhalf t htO.1).mp t.property⟩
      refine ⟨⟨H t, htQ, ?_⟩, hxV⟩
      change G (v (H.symm (H t))) = G y
      rw [H.left_inv htO.1, hvb t]
      exact congrArg G (congrArg Subtype.val (b.apply_symm_apply ⟨y, hy.1⟩))
    · rintro ⟨⟨y, hy, rfl⟩, hxV⟩
      refine ⟨?_, hxV⟩
      exact ⟨b ⟨H.symm y, hinverse y hy⟩,
        ⟨(b ⟨H.symm y, hinverse y hy⟩).property, htarget y hy⟩, (hvalue y hy).symm⟩
  obtain ⟨K, h0K, hKV, hKt, hK, hKi, hK0, hKA, hKS⟩ :=
    exists_pair_chart_of_finitePL_halfplane_patch hdim hf hinj hf0 h0Q B hB
      (fun _ hx => hx.2) isOpen_interior h0C
      (fun _ hx => ⟨fun h => h.2, fun h => ⟨interior_subset hx, h⟩⟩)
      A hA hfpositive hfzero hV h0V hfull
  let F := G.trans K
  have hFs : (b z : E) ∈ F.source := ⟨hzG, by
    change G (b z) ∈ K.source
    rw [hGz]
    exact h0K⟩
  have hFt : F.target = K.target := by
    apply inter_eq_left.mpr
    intro x hx
    exact (hKV (K.map_target hx)).1
  refine ⟨F, hFs, inter_subset_left, hFt.trans hKt, hK.comp hG,
    hGi.comp hKi, ?_, ?_, ?_⟩
  · change K (G (b z)) = 0
    rw [hGz, hK0]
  · intro x hx
    exact hKA (G x) hx.2
  · intro x hx
    have hmem : x ∈ S ↔ G x ∈ S' := by
      constructor
      · intro hs
        exact ⟨x, ⟨hs, hx.1⟩, rfl⟩
      · rintro ⟨y, hy, heq⟩
        exact G.injOn hy.2 hx.1 heq ▸ hy.1
    exact hmem.trans (hKS (G x) hx.2)

end PoincareConjecture.M76.HamiltonIndexOne
