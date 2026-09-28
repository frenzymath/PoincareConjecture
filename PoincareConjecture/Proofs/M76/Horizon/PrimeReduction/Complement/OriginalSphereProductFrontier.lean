import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalAnnulusDoubleProduct
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarShellMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInterior
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFiberRestriction

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "B" => frontier (halfBall 1)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (0 : ℝ) (1/8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7/8) 1

theorem original_sphere_product_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X}
    (H : U ≃ₜ (B ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (B ×ˢ I))
    (hσval : ∀ z : (B ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X)) :
    IsCompact U ∧
      (∀ z : (B ×ˢ I : Set (P3 × ℝ)),
        σ z ∈ interior U ↔ 0 < (z : P3 × ℝ).2 ∧ (z : P3 × ℝ).2 < 1) ∧
      frontier U = σ '' (B ×ˢ ({0,1} : Set ℝ)) := by
  have hpair : IsFinitePLBallPair P3 (halfBall 1) B := by
    rw [frontier_halfBall (Or.inl rfl)]
    exact isFinitePLBallPair_halfBall (Or.inl rfl)
  obtain ⟨C,hC,hCb⟩ := hpair.exists_cube_chart
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : P3 ≃L[ℝ] V3)
  have hCb' (x : halfBall 1) : (x : P3) ∈ B ↔ (C x : V3) ∈ Sphere := by
    simpa only [frontier_closedBall _ one_ne_zero] using hCb x
  obtain ⟨KS,hKS,hKSs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  let Q := C.restrictSubsets hpair.1 sphere_subset_closedBall hCb'
  have hQ : Q.IsFinitePL := hC.restrictSubsets_of_target
    hpair.1 sphere_subset_closedBall hCb' KS hKS hKSs
  have hQcopy := hQ
  obtain ⟨_,⟨L,hL,hLs,_⟩,_⟩ := hQcopy
  change L.space = B at hLs
  let qH : Sphere ≃ₜ L.space := Q.symm.trans (Homeomorph.setCongr hLs.symm)
  have hqH : qH.IsFinitePL := hQ.symm.setCongr rfl hLs.symm
  have hσimage : σ '' (B ×ˢ I) = U := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [hσval ⟨z,hz⟩]
      exact (H.symm ⟨z,hz⟩).property
    · intro x hx
      exact ⟨H ⟨x,hx⟩,(H ⟨x,hx⟩).property,
        (hσval _).trans (congrArg Subtype.val (H.symm_apply_apply _))⟩
  have hσemb : Topology.IsEmbedding (fun z : (B ×ˢ I : Set (P3 × ℝ)) => σ z) := by
    have heq : (fun z : (B ×ˢ I : Set (P3 × ℝ)) => σ z) =
        (fun z => (H.symm z : X)) := funext hσval
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp H.symm.isEmbedding
  obtain ⟨S,hS,_,hSnorm,_⟩ := exists_unitCube_inward_finitePL_collar
  have hc : PolyhedralPLInCharts e σ (L.space ×ˢ I) := by simpa only [hLs] using hσ
  have hci : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (P3 × ℝ)) => σ z) := by
    exact hσemb.comp (Homeomorph.setCongr (congrArg (fun A => A ×ˢ I) hLs)).isEmbedding
  obtain ⟨f,hf,hfi,hfimage,hfval⟩ := exists_original_collar_shell_map L σ hc hci qH hqH S hS
    (show (0 : ℝ) < 1 by norm_num) (le_refl 1)
  have hfU : f '' T = U := by simpa only [hLs,hσimage] using hfimage
  have hTeq : T = closedBall (0 : V3) 1 ∩ (ball (0 : V3) (7/8))ᶜ := by
    ext x
    simp only [mem_preimage,mem_Icc,mem_inter_iff,mem_compl_iff,
      mem_closedBall,mem_ball,dist_zero_right,not_lt]
    tauto
  have hTcompact : IsCompact T := by
    rw [hTeq]
    exact (isCompact_closedBall (0 : V3) 1).inter_right isOpen_ball.isClosed_compl
  have hTi (x : V3) : x ∈ interior T ↔ 7/8 < ‖x‖ ∧ ‖x‖ < 1 := by
    rw [hTeq,interior_inter,interior_closedBall _ one_ne_zero,interior_compl,
      closure_ball _ (by norm_num : (7/8 : ℝ) ≠ 0)]
    simp only [mem_inter_iff,mem_compl_iff,mem_closedBall,mem_ball,dist_zero_right,not_le]
    tauto
  let : CompactSpace T := isCompact_iff_compactSpace.mp hTcompact
  have hfemb : Topology.IsEmbedding (fun x : T => f x) :=
    (hf.continuousOn.domRestrict.isClosedEmbedding
      (fun x y h => Subtype.ext (hfi x.property y.property h))).isEmbedding
  have hUcompact : IsCompact U := by
    rw [←hfU]
    exact hTcompact.image_of_continuousOn hf.continuousOn
  have hinterior (z : (B ×ˢ I : Set (P3 × ℝ))) :
      σ z ∈ interior U ↔ 0 < (z : P3 × ℝ).2 ∧ (z : P3 × ℝ).2 < 1 := by
    let base : L.space := ⟨(z : P3 × ℝ).1,hLs.symm.subset z.property.1⟩
    let v : (Sphere ×ˢ J : Set (V3 × ℝ)) :=
      ⟨((qH.symm base : V3),(z : P3 × ℝ).2/8),
        (qH.symm base).property,by linarith [z.property.2.1],by linarith [z.property.2.2]⟩
    have ht : 8 * (1 : ℝ) * ((z : P3 × ℝ).2/8) = (z : P3 × ℝ).2 := by ring
    have hvalue : f (S v) = σ z := by
      rw [hfval]
      change σ ((qH (qH.symm base) : P3),8*1*((z : P3 × ℝ).2/8)) = σ z
      rw [qH.apply_symm_apply,ht]
    have hi := hf.mem_interior_image_iff rfl hfemb (S v)
    rw [hfU,hvalue,hTi,hSnorm] at hi
    change (σ z ∈ interior U ↔ 7/8 < 1-(z : P3 × ℝ).2/8 ∧
      1-(z : P3 × ℝ).2/8 < 1) at hi
    exact hi.trans (by constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith)
  refine ⟨hUcompact,hinterior,?_⟩
  ext x
  constructor
  · intro hx
    have hxU : x ∈ U := hUcompact.isClosed.frontier_subset hx
    let z := H ⟨x,hxU⟩
    have hzval : σ z = x := (hσval z).trans
      (congrArg Subtype.val (H.symm_apply_apply ⟨x,hxU⟩))
    have hznot : ¬ (0 < (z : P3 × ℝ).2 ∧ (z : P3 × ℝ).2 < 1) := by
      intro hz
      exact hx.2 (hzval ▸ (hinterior z).mpr hz)
    refine ⟨z,⟨z.property.1,?_⟩,hzval⟩
    change (z : P3 × ℝ).2 = 0 ∨ (z : P3 × ℝ).2 = 1
    rcases le_or_gt (z : P3 × ℝ).2 0 with h | h
    · exact Or.inl (le_antisymm h z.property.2.1)
    · exact Or.inr (le_antisymm z.property.2.2 (le_of_not_gt (fun h' => hznot ⟨h,h'⟩)))
  · rintro ⟨z,⟨hzB,hzt⟩,rfl⟩
    have ht : z.2 = 0 ∨ z.2 = 1 := hzt
    have hz : z ∈ B ×ˢ I := ⟨hzB,by rcases ht with h | h <;> rw [h] <;> norm_num⟩
    rw [frontier,hUcompact.isClosed.closure_eq]
    refine ⟨hσimage.subset ⟨z,hz,rfl⟩,?_⟩
    intro hi
    have h := (hinterior ⟨z,hz⟩).mp hi
    rcases ht with ht | ht <;> dsimp at h <;> linarith [h.1,h.2]

theorem original_marked_sphere_product_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X}
    (H : U ≃ₜ (B ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (B ×ˢ I))
    (hσval : ∀ z : (B ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X))
    (S : Bool → Set X) (hSU : ∀ s, S s ⊆ U)
    (hmark : ∀ s (x : U), (x : X) ∈ S s ↔
      (H x : P3 × ℝ).2 = if s then (1 : ℝ) else 0) :
    IsCompact U ∧ frontier U = S false ∪ S true := by
  obtain ⟨hU,_,hfront⟩ := original_sphere_product_frontier H σ hσ hσval
  refine ⟨hU,?_⟩
  rw [hfront]
  ext x
  constructor
  · rintro ⟨z,⟨hzB,hzt⟩,rfl⟩
    have ht : z.2 = 0 ∨ z.2 = 1 := hzt
    have hz : z ∈ B ×ˢ I := ⟨hzB,by rcases ht with h | h <;> rw [h] <;> norm_num⟩
    have hσU : σ z ∈ U := (hσval ⟨z,hz⟩).symm ▸ (H.symm ⟨z,hz⟩).property
    have hHσ : H ⟨σ z,hσU⟩ = ⟨z,hz⟩ := by
      have hsub : (⟨σ z,hσU⟩ : U) = H.symm ⟨z,hz⟩ := Subtype.ext (hσval ⟨z,hz⟩)
      rw [hsub,H.apply_symm_apply]
    rcases ht with ht | ht
    · exact Or.inl ((hmark false ⟨σ z,hσU⟩).mpr (by simpa [hHσ] using ht))
    · exact Or.inr ((hmark true ⟨σ z,hσU⟩).mpr (by simpa [hHσ] using ht))
  · intro hx
    have hside (s : Bool) (hxs : x ∈ S s) : x ∈ σ '' (B ×ˢ ({0,1} : Set ℝ)) := by
      let y : U := ⟨x,hSU s hxs⟩
      have ht := (hmark s y).mp hxs
      refine ⟨H y,⟨(H y).property.1,?_⟩,
        (hσval _).trans (congrArg Subtype.val (H.symm_apply_apply y))⟩
      change (H y : P3 × ℝ).2 = 0 ∨ (H y : P3 × ℝ).2 = 1
      rw [ht]
      cases s <;> simp
    exact hx.elim (hside false) (hside true)

end PoincareConjecture.M76
