import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereProductDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FinitePLBallAttachment

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Base" => frontier (halfBall 1)
local notation "I" => Icc (0 : ℝ) 1

theorem original_selected_product_endpoint_geometry
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U S : Set X}
    (W : U ≃ₜ (Base ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (Base ×ˢ I))
    (hσval : ∀ z : (Base ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X))
    (b : Bool) (hSU : S ⊆ U)
    (hmark : ∀ x : U, (x : X) ∈ S ↔
      (W x : P3 × ℝ).2 = if b then (1 : ℝ) else 0) :
    IsConnected U ∧
      ∃ (T : Set X) (_sT : ChartwisePLSphere e T),
        frontier U = S ∪ T ∧ Disjoint S T := by
  have hpair : IsFinitePLBallPair P3 (halfBall 1) Base := by
    rw [frontier_halfBall (Or.inl rfl)]
    exact isFinitePLBallPair_halfBall (Or.inl rfl)
  obtain ⟨C,_,hCb⟩ := hpair.exists_cube_chart
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : P3 ≃L[ℝ] V3)
  let db := C.restrictSubsets hpair.1 isClosed_closedBall.frontier_subset hCb
  have hBc : IsConnected Base := db.isConnected_of_convex_frontier
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp)
  have himage : σ '' (Base ×ˢ I) = U := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (hσval ⟨z,hz⟩).symm ▸ (W.symm ⟨z,hz⟩).property
    · intro x hx
      exact ⟨W ⟨x,hx⟩,(W ⟨x,hx⟩).property,
        (hσval _).trans (congrArg Subtype.val (W.symm_apply_apply _))⟩
  have hUc : IsConnected U := himage ▸
    (hBc.prod (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))).image _ hσ.continuousOn
  let T := σ '' (Base ×ˢ {if b then (0 : ℝ) else 1})
  have hbt : (if b then (0 : ℝ) else 1) ∈ I := by cases b <;> norm_num
  obtain ⟨sT⟩ := original_sphere_product_endpoint W σ hσ hσval hbt
  have hvalue (z : (Base ×ˢ I : Set (P3 × ℝ))) :
      W ⟨σ z,(hσval z).symm ▸ (W.symm z).property⟩ = z := by
    have hx : (⟨σ z,(hσval z).symm ▸ (W.symm z).property⟩ : U) = W.symm z :=
      Subtype.ext (hσval z)
    rw [hx,W.apply_symm_apply]
  have hTmark (x : U) : (x : X) ∈ T ↔
      (W x : P3 × ℝ).2 = if b then (0 : ℝ) else 1 := by
    constructor
    · rintro ⟨z,hz,hzx⟩
      have hzI : z ∈ Base ×ˢ I := ⟨hz.1,hz.2 ▸ hbt⟩
      have hxx : x = ⟨σ z,(hσval ⟨z,hzI⟩).symm ▸ (W.symm ⟨z,hzI⟩).property⟩ :=
        Subtype.ext hzx.symm
      rw [hxx,hvalue ⟨z,hzI⟩]
      exact hz.2
    · intro hx
      exact ⟨W x,⟨(W x).property.1,hx⟩,
        (hσval _).trans (congrArg Subtype.val (W.symm_apply_apply x))⟩
  have hTU : T ⊆ U := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hσval ⟨z,hz.1,hz.2 ▸ hbt⟩).symm ▸ (W.symm ⟨z,hz.1,hz.2 ▸ hbt⟩).property
  obtain ⟨hU,_,hfront⟩ := original_sphere_product_frontier W σ hσ hσval
  refine ⟨hUc,T,sT,?_,?_⟩
  · rw [hfront]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzt : z.2 = 0 ∨ z.2 = 1 := hz.2
      have hzI : z ∈ Base ×ˢ I := ⟨hz.1,by rcases hzt with h | h <;> rw [h] <;> norm_num⟩
      let y : U := ⟨σ z,(hσval ⟨z,hzI⟩).symm ▸ (W.symm ⟨z,hzI⟩).property⟩
      have hy := hvalue ⟨z,hzI⟩
      change W y = ⟨z,hzI⟩ at hy
      change (y : X) ∈ S ∪ T
      rw [mem_union,hmark,hTmark,hy]
      cases b <;> simpa [or_comm] using hzt
    · intro hx
      have hxU : x ∈ U := hx.elim (fun h => hSU h) (fun h => hTU h)
      let y : U := ⟨x,hxU⟩
      have hzt : (W y : P3 × ℝ).2 = 0 ∨ (W y : P3 × ℝ).2 = 1 := by
        rcases hx with hs | ht
        · have hh := (hmark y).mp hs
          cases b <;> simp_all
        · have hh := (hTmark y).mp ht
          cases b <;> simp_all
      exact ⟨W y,⟨(W y).property.1,hzt⟩,
        (hσval _).trans (congrArg Subtype.val (W.symm_apply_apply y))⟩
  · apply disjoint_left.mpr
    intro x hxS hxT
    have hs := (hmark ⟨x,hSU hxS⟩).mp hxS
    have ht := (hTmark ⟨x,hSU hxS⟩).mp hxT
    cases b <;> simp_all

end PoincareConjecture.M76
