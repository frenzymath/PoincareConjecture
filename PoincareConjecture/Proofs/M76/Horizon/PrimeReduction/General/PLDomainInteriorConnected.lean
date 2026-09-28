import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex












set_option autoImplicit false
open Set Metric

namespace OpenPartialHomeomorph

private theorem exists_open_preconnected_inter_of_affine_pos
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : OpenPartialHomeomorph X E) {P : Set X} (ell : E →ᴬ[ℝ] ℝ)
    (hpos : ∀ y ∈ H.source, y ∈ P ↔ 0 < ell (H y))
    {x : X} (hxH : x ∈ H.source) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreconnected (U ∩ P) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp H.open_target (H x) (H.map_source hxH)
  let U := H.source ∩ H ⁻¹' ball (H x) r
  let T := ball (H x) r ∩ (ell : E → ℝ) ⁻¹' Ioi 0
  have hT : T ⊆ H.target := fun _ hy => hball hy.1
  have hconn : IsPreconnected T :=
    ((convex_ball (H x) r).inter
      (Convex.affine_preimage ell.toAffineMap (convex_Ioi (0 : ℝ)))).isPreconnected
  have himage : U ∩ P = H.symm '' T := by
    apply Subset.antisymm
    · rintro y ⟨⟨hyH, hyball⟩, hyP⟩
      exact ⟨H y, ⟨hyball, (hpos y hyH).mp hyP⟩, H.left_inv hyH⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyH := H.map_target (hT hy)
      refine ⟨⟨hyH, ?_⟩, (hpos _ hyH).mpr ?_⟩
      · change H (H.symm y) ∈ ball (H x) r
        rw [H.right_inv (hT hy)]
        exact hy.1
      · rw [H.right_inv (hT hy)]
        exact hy.2
  refine ⟨U, H.isOpen_inter_preimage isOpen_ball, ⟨hxH, mem_ball_self hr⟩, ?_⟩
  rw [himage]
  exact hconn.image _ (H.symm.continuousOn.mono hT)

end OpenPartialHomeomorph

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)



theorem PLDomain.exists_open_preconnected_inter_interior
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {P : Set X}
    (he : PLDomain e P) {x : X} (hx : x ∈ P) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreconnected (U ∩ interior P) := by
  by_cases hxB : x ∈ frontier P
  · obtain ⟨ell, v, H, hv, hxH, _, _, hhalf⟩ := he.halfspace x hxB
    have hi := H.isImage_interior_of_affine_nonneg ell v hv hhalf
    exact H.exists_open_preconnected_inter_of_affine_pos ell
      (fun y hy => (hi.apply_mem_iff hy).symm) hxH
  · have hxI := (mem_interior_iff_notMem_frontier hx).mpr hxB
    obtain ⟨j, hxj⟩ := he.cover x
    let H := (e j).restrOpen (interior P) isOpen_interior
    let ell : V3 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ V3 1
    have hpos : ∀ y ∈ H.source, y ∈ interior P ↔ 0 < ell (H y) := by
      intro y hy
      exact iff_of_true hy.2 zero_lt_one
    exact H.exists_open_preconnected_inter_of_affine_pos ell hpos ⟨hxj, hxI⟩



theorem PLDomain.isConnected_interior
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {P : Set X}
    (he : PLDomain e P) (hconn : IsConnected P) : IsConnected (interior P) := by
  refine ⟨closure_nonempty_iff.mp (he.closure_interior.symm ▸ hconn.nonempty), ?_⟩
  intro u v hu hv hcover hune hvne
  have hdecomp : interior P = (interior P ∩ u) ∪ (interior P ∩ v) := by
    ext x
    constructor
    · intro hx
      exact (hcover hx).elim (fun hxu => Or.inl ⟨hx, hxu⟩) (fun hxv => Or.inr ⟨hx, hxv⟩)
    · exact fun hx => hx.elim And.left And.left
  have hclosedCover : P ⊆ closure (interior P ∩ u) ∪ closure (interior P ∩ v) := by
    have hh := congrArg closure hdecomp
    rw [he.closure_interior, closure_union] at hh
    exact hh.subset
  obtain ⟨x, hxP, hxclu, hxclv⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected
    _ _ isClosed_closure isClosed_closure hclosedCover
    (by obtain ⟨x, hx⟩ := hune; exact ⟨x, interior_subset hx.1, subset_closure hx⟩)
    (by obtain ⟨x, hx⟩ := hvne; exact ⟨x, interior_subset hx.1, subset_closure hx⟩)
  obtain ⟨U, hU, hxU, hlocal⟩ := he.exists_open_preconnected_inter_interior hxP
  obtain ⟨y, hyU, hyI, hyu⟩ := mem_closure_iff.mp hxclu U hU hxU
  obtain ⟨z, hzU, hzI, hzv⟩ := mem_closure_iff.mp hxclv U hU hxU
  obtain ⟨w, ⟨_, hwI⟩, hwu, hwv⟩ := hlocal u v hu hv
    (fun _ h => hcover h.2) ⟨y, ⟨hyU, hyI⟩, hyu⟩ ⟨z, ⟨hzU, hzI⟩, hzv⟩
  exact ⟨w, hwI, hwu, hwv⟩

end PoincareConjecture.M76
