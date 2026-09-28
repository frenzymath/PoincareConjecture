import PoincareConjecture.Proofs.M76.Mathlib.SmallConvexHalfspaceNeighborhood
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms












set_option autoImplicit false

open Set Metric Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] [Nonempty ι]






theorem IsCompact.exists_convex_halfspace_frontier_neighborhood
    {S U : Set E} (hS : IsCompact S) (hcvS : Convex ℝ S)
    (hzeroS : (0 : E) ∈ S) (hU : IsOpen U) (hSU : S ⊆ U)
    (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ (C : Set E) (L : Finset (E →ₗ[ℝ] ℝ)) (J : SimplicialComplex ℝ E),
      IsCompact C ∧ Convex ℝ C ∧ S ⊆ interior C ∧ C ⊆ U ∧
      L.Nonempty ∧ (∀ A ∈ L, A ≠ 0) ∧ C = {x | ∀ A ∈ L, A x ≤ 1} ∧
      J.faces.Finite ∧ J.space = frontier C := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨R, hR, hSnorm⟩ := (hS.image c.continuous).isBounded.exists_pos_norm_lt
  let B : Set E := c ⁻¹' closedBall (0 : ι → ℝ) R
  have hB : IsCompact B := c.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  let G : (ι ⊕ ι) → E →ₗ[ℝ] ℝ := fun i =>
    R⁻¹ • (signedCubeCoordinate i).comp c.toLinearMap
  have hG (i : ι ⊕ ι) : G i ≠ 0 := by
    intro he
    apply signedCubeCoordinate_ne_zero i
    apply LinearMap.ext
    intro y
    have h := congrArg (fun f : E →ₗ[ℝ] ℝ => f (c.symm y)) he
    change R⁻¹ * signedCubeCoordinate i (c (c.symm y)) = 0 at h
    rw [c.apply_symm_apply] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hR.ne')
  have hGS (x : E) (hx : x ∈ S) (i : ι ⊕ ι) : G i x < 1 := by
    change R⁻¹ * signedCubeCoordinate i (c x) < 1
    rw [← div_eq_inv_mul, div_lt_one hR]
    exact (signedCubeCoordinate_le_norm i (c x)).trans_lt
      (hSnorm (c x) (mem_image_of_mem c hx))
  have hBG : B = {x | ∀ i, G i x ≤ 1} := by
    ext x
    change ‖c x - 0‖ ≤ R ↔ ∀ i, G i x ≤ 1
    rw [sub_zero]
    have hform (i : ι ⊕ ι) : G i x ≤ 1 ↔ signedCubeCoordinate i (c x) ≤ R := by
      change R⁻¹ * signedCubeCoordinate i (c x) ≤ 1 ↔ _
      rw [← div_eq_inv_mul, div_le_one hR]
    simp_rw [hform]
    constructor
    · exact fun hx i => (signedCubeCoordinate_le_norm i (c x)).trans hx
    · intro hx
      apply (pi_norm_le_iff_of_nonneg hR.le).mpr
      intro i
      rw [Real.norm_eq_abs]
      have hp : c x i ≤ R := hx (.inl i)
      have hn : -c x i ≤ R := hx (.inr i)
      exact abs_le.mpr ⟨by linarith, hp⟩
  let D := B \ U
  have hD : IsCompact D := hB.inter_right hU.isClosed_compl
  have hseparate (p : D) : ∃ f : E →ₗ[ℝ] ℝ,
      f ≠ 0 ∧ (∀ x ∈ S, f x < 1) ∧ 1 < f p := by
    obtain ⟨g, b, hgS, hgp⟩ := geometric_hahn_banach_closed_point hcvS hS.isClosed
      (show (p : E) ∉ S from fun hp => p.property.2 (hSU hp))
    have hb : 0 < b := by simpa only [map_zero] using hgS 0 hzeroS
    let f : E →ₗ[ℝ] ℝ := b⁻¹ • g.toLinearMap
    have hfp : 1 < f p := by
      change 1 < b⁻¹ * g p
      rw [← div_eq_inv_mul, one_lt_div hb]
      exact hgp
    refine ⟨f, ?_, ?_, hfp⟩
    · intro hf
      rw [hf, LinearMap.zero_apply] at hfp
      exact (by norm_num : ¬ (1 : ℝ) < 0) hfp
    · intro x hx
      change b⁻¹ * g x < 1
      rw [← div_eq_inv_mul, div_lt_one hb]
      exact hgS x hx
  choose f hf hfS hfp using hseparate
  obtain ⟨T, hT⟩ := hD.elim_finite_subcover (fun p : D => {x | 1 < f p x})
    (fun p => isOpen_lt continuous_const (f p).continuous_of_finiteDimensional)
    (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hfp ⟨p, hp⟩⟩)
  let L : Finset (E →ₗ[ℝ] ℝ) := Finset.univ.image G ∪ T.image f
  have hLne : L.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨G (.inl i), Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨.inl i, Finset.mem_univ _, rfl⟩)⟩
  have hL (A : E →ₗ[ℝ] ℝ) (hA : A ∈ L) : A ≠ 0 := by
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      exact hG i
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hA
      exact hf p
  have hLS (x : E) (hx : x ∈ S) (A : E →ₗ[ℝ] ℝ) (hA : A ∈ L) : A x < 1 := by
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      exact hGS x hx i
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hA
      exact hfS p x hx
  let C : Set E := {x | ∀ A ∈ L, A x ≤ 1}
  have hCclosed : IsClosed C := by
    simp only [C, ofPred_forall]
    exact isClosed_biInter fun A _ =>
      isClosed_le A.continuous_of_finiteDimensional continuous_const
  have hCB : C ⊆ B := by
    intro x hx
    rw [hBG]
    intro i
    exact hx (G i) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hC : IsCompact C := hB.of_isClosed_subset hCclosed hCB
  have hcv : Convex ℝ C := by
    simp only [C, ofPred_forall]
    exact convex_iInter fun A => convex_iInter fun _ =>
      (convex_Iic (1 : ℝ)).linear_preimage A
  have hSC : S ⊆ interior C := by
    have hopen : IsOpen {x : E | ∀ A ∈ L, A x < 1} := by
      simp only [ofPred_forall]
      exact isOpen_biInter_finset fun A _ =>
        isOpen_lt A.continuous_of_finiteDimensional continuous_const
    have hsub : {x : E | ∀ A ∈ L, A x < 1} ⊆ C :=
      fun x hx A hA => (hx A hA).le
    exact fun x hx => interior_maximal hsub hopen (hLS x hx)
  have hCU : C ⊆ U := by
    intro x hx
    by_contra hxU
    obtain ⟨p, hpT, hxp⟩ := mem_iUnion₂.mp (hT ⟨hCB hx, hxU⟩)
    exact (not_lt_of_ge (hx (f p)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hpT, rfl⟩)))) hxp
  let H : Finset (E →ᵃ[ℝ] ℝ) :=
    L.image fun A => A.toAffineMap - AffineMap.const ℝ E 1
  have hrepA : C = {x | ∀ A ∈ H, A x ≤ 0} := by
    ext x
    simp only [C, H, mem_setOf_eq, Finset.forall_mem_image,
      AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
      AffineMap.const_apply, sub_nonpos]
  obtain ⟨K, hK, hKC⟩ := hC.exists_finite_triangulation_of_halfspaces H hrepA
  exact ⟨C, L, K.frontierSubcomplex C, hC, hcv, hSC, hCU, hLne, hL, rfl,
    K.frontierSubcomplex_finite C hK,
    K.frontierSubcomplex_space hCclosed hcv ⟨0, hSC hzeroS⟩ hKC⟩

end Set
