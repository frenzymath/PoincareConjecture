import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel
import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) {β : Type*}

local notation "X" => LatticeHandleAmbient ι κ L
local notation "R" => latticeHandleDomain ι κ L
local notation "V3" => (Fin 3 → ℝ)

omit [Fintype κ] in




theorem StandardLatticeHandleAtlas.chartwisePLOn_identity_of_restricted_charts
    (d : β → OpenPartialHomeomorph X V3) (hd : StandardLatticeHandleAtlas ι κ L d)
    (charts : Set (OpenPartialHomeomorph X V3))
    (he : PLDomain (fun c : charts => (c : OpenPartialHomeomorph X V3)) R)
    {O : Set X} (hO : IsOpen O)
    (hmem : ∀ j, (d j).restrOpen O hO ∈ charts) :
    ChartwisePLOn (fun c : charts => (c : OpenPartialHomeomorph X V3)) d
      (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' O) := by
  classical
  refine ⟨he, hd.domain, hO.preimage continuous_subtype_val, ?_⟩
  intro x hx
  obtain ⟨j, hxj⟩ := hd.domain.cover (x : X)
  let i : charts := ⟨(d j).restrOpen O hO, hmem j⟩
  obtain ⟨a, ha⟩ := hd.inverse_formula j
  have hdomain (z : V3) (hz : z ∈ (d j).target) :
      (d j).symm z ∈ R ↔ (a z).1 ∈ closedBall (0 : ι → ℝ) 1 := by
    rw [ha z hz]
    simp only [latticeHandleDomain, mem_prod, mem_univ, and_true]
  let T : Set V3 := (d j).target ∩ (d j).symm ⁻¹' O
  have hT : IsOpen T :=
    (d j).continuousOn_invFun.isOpen_inter_preimage (d j).open_target hO
  have hxT : d j x ∈ T := by
    refine ⟨(d j).map_source hxj, ?_⟩
    change (d j).symm (d j x) ∈ O
    rw [(d j).left_inv hxj]
    exact hx
  obtain ⟨K, hK, hxK, hKT⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    (isCompact_singleton : IsCompact ({d j x} : Set V3)) hT
    (singleton_subset_iff.mpr hxT)
  let f : V3 →ᴬ[ℝ] (ι → ℝ) :=
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ)).toContinuousAffineMap.comp
      a.toContinuousAffineMap
  let A : (ι ⊕ ι) → V3 →ᵃ[ℝ] ℝ := fun k =>
    (signedCubeCoordinate k).toAffineMap.comp f.toAffineMap - AffineMap.const ℝ V3 1
  let H : Finset (V3 →ᵃ[ℝ] ℝ) := Finset.univ.image A
  have hhalf (z : V3) : (∀ b ∈ H, b z ≤ 0) ↔
      (a z).1 ∈ closedBall (0 : ι → ℝ) 1 := by
    rw [closedBall_eq_signedCube_halfspaces]
    simp only [H, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, A, AffineMap.coe_sub, Pi.sub_apply,
      AffineMap.comp_apply, AffineMap.const_apply, sub_nonpos]
    rfl
  obtain ⟨J, hJ, hJspace⟩ := K.exists_finite_triangulation_inter_halfspaces hK H
  have hJK : J.space ⊆ K.space := hJspace.subset.trans inter_subset_left
  have hJR (z : V3) (hz : z ∈ J.space) : (d j).symm z ∈ R :=
    (hdomain z (hKT (hJK hz)).1).mpr ((hhalf z).mp (hJspace.subset hz).2)
  let V0 : Set R := (Subtype.val : R → X) ⁻¹' ((d j).source ∩ O)
  have hV0 : IsOpen V0 := ((d j).open_source.inter hO).preimage continuous_subtype_val
  let V : Set R := V0 ∩ (fun y : R => d j y) ⁻¹' interior K.space
  have hV : IsOpen V := by
    have hc : ContinuousOn (fun y : R => d j y) V0 :=
      (d j).continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy.1)
    exact hc.isOpen_inter_preimage hV0 isOpen_interior
  have hxV : x ∈ V := ⟨⟨hxj, hx⟩, hxK (mem_singleton _)⟩
  have hVJ (y : R) (hy : y ∈ V) : d j y ∈ J.space := by
    apply hJspace.symm.subset
    refine ⟨interior_subset hy.2, (hhalf _).mpr ?_⟩
    apply (hdomain _ ((d j).map_source hy.1.1)).mp
    rw [(d j).left_inv hy.1.1]
    exact y.property
  refine ⟨i, j, J, V, id, hJ, hV, hxV, fun _ hy => hy.1.2,
    fun _ hy => hy.1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact hVJ y hy
  · intro z hz
    exact hKT (hJK hz)
  · intro z hz
    exact ⟨⟨(d j).symm z, hJR z hz⟩, (hKT (hJK hz)).2, rfl⟩
  · exact ⟨J, hJ, rfl, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩
  · intro y hy _
    exact ⟨hy.1, rfl⟩

end PoincareConjecture.M76
