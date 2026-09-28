import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalConfinedSphereBall

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76

theorem closure_subset_closedBall_of_frontier_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsCompact (closure U)) {r : ℝ} (hr : 0 ≤ r)
    (hfront : frontier U ⊆ closedBall (0 : E) r) :
    closure U ⊆ closedBall (0 : E) r := by
  intro x hx
  obtain ⟨y,hy,hmax⟩ := hU.exists_isMaxOn ⟨x,hx⟩ continuous_norm.continuousOn
  suffices hybound : ‖y‖ ≤ r by
    exact mem_closedBall_zero_iff.mpr ((hmax hx).trans hybound)
  by_contra hn
  have hry : r < ‖y‖ := lt_of_not_ge hn
  have hyn : 0 < ‖y‖ := hr.trans_lt hry
  have hyint : y ∈ interior U := by
    by_contra h
    exact (not_le_of_gt hry) (mem_closedBall_zero_iff.mp (hfront ⟨hy,h⟩))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hyint)
  let δ : ℝ := ε / (2 * ‖y‖)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hyn)
  have hδnorm : δ * ‖y‖ = ε / 2 := by
    dsimp [δ]
    field_simp
  have hnear : y + δ • y ∈ ball y ε := by
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos hδ,hδnorm]
    linarith
  have hle := hmax (subset_closure (hball hnear))
  change ‖y + δ • y‖ ≤ ‖y‖ at hle
  have heq : y + δ • y = (1 + δ) • y := by rw [add_smul,one_smul]
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < 1 + δ)] at hle
  nlinarith [mul_pos hδ hyn]

open Geometry
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Cube" => closedBall (0 : V3) 1

private theorem finitePLBallPair_double_cube :
    IsFinitePLBallPair V3 (closedBall (0 : V3) 2) (frontier (closedBall (0 : V3) 2)) := by
  classical
  let A : Fin 3 ⊕ Fin 3 → V3 →ᵃ[ℝ] ℝ := fun i =>
    (signedCubeCoordinate i).toAffineMap - AffineMap.const ℝ V3 2
  let H := Finset.univ.image A
  have hrep : closedBall (0 : V3) 2 = {x | ∀ a ∈ H, a x ≤ 0} := by
    ext x
    constructor
    · intro hx a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact sub_nonpos.mpr ((signedCubeCoordinate_le_norm i x).trans
        (mem_closedBall_zero_iff.mp hx))
    · intro hx
      have hs (i : Fin 3 ⊕ Fin 3) : signedCubeCoordinate i x ≤ 2 :=
        sub_nonpos.mp (hx (A i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
      apply mem_closedBall_zero_iff.mpr
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro i
      rw [Real.norm_eq_abs,abs_le]
      exact ⟨neg_le.mp (hs (Sum.inr i)),hs (Sum.inl i)⟩
  exact isFinitePLBallPair_of_affine_halfspaces (isCompact_closedBall _ _) H hrep
    ⟨0,ball_subset_interior_closedBall (mem_ball_self (by norm_num : (0 : ℝ) < 2))⟩

theorem ChartwisePLSphere.exists_original_closed_ball_filling
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {S B R : Set X} (s : ChartwisePLSphere e S) (b : ChartwisePLBall e B R)
    (hSB : S ⊆ B) :
    ∃ D : Set X, D ⊆ B ∧ Nonempty (ChartwisePLBall e D S) := by
  classical
  have hsS (x : V3) (hx : x ∈ Sphere) : s.map x ∈ S := by
    rw [s.map_eq ⟨x,hx⟩]
    exact (s.parametrization ⟨x,hx⟩).property
  have hbi : InjOn b.map Cube := by
    intro x hx y hy hxy
    rw [b.map_eq ⟨x,hx⟩,b.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (b.parametrization.injective (Subtype.ext hxy))
  let q : V3 → V3 := fun x => if hx : x ∈ Sphere then
    b.parametrization.symm ⟨s.map x,hSB (hsS x hx)⟩ else 0
  have hqval (x : Sphere) : q x =
      (b.parametrization.symm ⟨s.map x,hSB (hsS x x.property)⟩ : V3) := by
    simp only [q,dif_pos x.property]
  have hqCube : MapsTo q Sphere Cube := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (b.parametrization.symm ⟨s.map x,hSB (hsS x hx)⟩).property
  have hvalue (x : V3) (hx : x ∈ Sphere) : b.map (q x) = s.map x := by
    rw [hqval ⟨x,hx⟩,b.map_eq]
    exact congrArg Subtype.val (b.parametrization.apply_symm_apply _)
  have hqc : ContinuousOn q Sphere := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (b.parametrization.symm.continuous.comp
      (s.piecewiseAffine.continuousOn.domRestrict.subtype_mk
        (fun x => hSB (hsS x x.property))))
    convert h using 1
    funext x
    exact hqval x
  obtain ⟨A,hA,hAS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hq : FinitePiecewiseAffineOn q Sphere := by
    rw [←hAS]
    exact b.piecewiseAffine.finitePiecewiseAffineOn_lift he hbi A hA
      (hqc.mono hAS.subset) (fun x hx => hqCube (hAS.subset hx))
      ((s.piecewiseAffine.restrict_finite A hA hAS.subset).congr
        (fun x hx => (hvalue x (hAS.subset hx)).symm))
  have hqi : InjOn q Sphere := by
    intro x hx y hy hxy
    have heq := congrArg b.map hxy
    rw [hvalue x hx,hvalue y hy,s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at heq
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext heq))
  have hqint : q '' Sphere ⊆ interior (closedBall (0 : V3) 2) := by
    rintro _ ⟨x,hx,rfl⟩
    apply ball_subset_interior_closedBall
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hqCube hx)).trans_lt (by norm_num))
  obtain ⟨H,hH,_⟩ := hq.exists_homeomorph_image hqi
  have hchart : ∃ G : (q '' Sphere) ≃ₜ frontier Cube, G.IsFinitePL := by
    rw [frontier_closedBall _ one_ne_zero]
    exact ⟨H.symm,hH.symm⟩
  obtain ⟨G,hG⟩ := hchart
  obtain ⟨K,_,hK,hKC,_,_⟩ :=
    Set.IsFinitePLBallPair.exists_finite_carrier_and_rim_complexes
      finitePLBallPair_double_cube
  obtain ⟨U,_,_,hfront,hUC,hUB,_⟩ := hG.hasAlexanderRegionBalls
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp) (by simp)
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self (by norm_num : (0 : ℝ) < 2))⟩
    hqint K hK hKC
  have hUCube : closure U ⊆ Cube :=
    closure_subset_closedBall_of_frontier_subset
      ((isCompact_closedBall (0 : V3) 2).of_isClosed_subset isClosed_closure
        (hUC.trans interior_subset)) zero_le_one (by
          rw [hfront]
          rintro _ ⟨x,hx,rfl⟩
          exact hqCube hx)
  have hback : b.map '' (q '' Sphere) = S := by
    apply Subset.antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      rw [hvalue x hx]
      exact hsS x hx
    · intro x hx
      let y := s.parametrization.symm ⟨x,hx⟩
      refine ⟨q y,⟨y,y.property,rfl⟩,?_⟩
      rw [hvalue y y.property,s.map_eq y]
      exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨x,hx⟩)
  have hball := exists_chartwisePLBall_image hUB
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]))
    b.piecewiseAffine hUCube hbi
  rw [hback] at hball
  refine ⟨b.map '' closure U,?_,hball⟩
  rintro _ ⟨x,hx,rfl⟩
  rw [b.map_eq ⟨x,hUCube hx⟩]
  exact (b.parametrization ⟨x,hUCube hx⟩).property

end PoincareConjecture.M76
