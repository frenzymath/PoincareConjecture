import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereProductFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "B" => frontier (halfBall 1)
local notation "I" => Icc (0 : ℝ) 1

theorem original_sphere_product_regularClosed
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X}
    (H : U ≃ₜ (B ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (B ×ˢ I))
    (hσval : ∀ z : (B ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X)) :
    closure (interior U) = U := by
  obtain ⟨hU,hi,_⟩ := original_sphere_product_frontier H σ hσ hσval
  have hc : closure (B ×ˢ Ioo (0 : ℝ) 1) = B ×ˢ I := by
    rw [closure_prod_eq,isClosed_frontier.closure_eq,closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hmap : MapsTo σ (B ×ˢ Ioo (0 : ℝ) 1) (interior U) := by
    intro z hz
    exact (hi ⟨z,hz.1,le_of_lt hz.2.1,le_of_lt hz.2.2⟩).mpr hz.2
  have hclosure := hmap.closure_of_continuousOn (hc.symm ▸ hσ.continuousOn)
  apply Subset.antisymm (closure_minimal interior_subset hU.isClosed)
  intro x hx
  have hz : (H ⟨x,hx⟩ : P3 × ℝ) ∈ closure (B ×ˢ Ioo (0 : ℝ) 1) :=
    hc.symm.subset (H ⟨x,hx⟩).property
  have hval := (hσval (H ⟨x,hx⟩)).trans
    (congrArg Subtype.val (H.symm_apply_apply ⟨x,hx⟩))
  simpa only [hval] using hclosure hz

theorem original_sphere_product_endpoint
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X}
    (H : U ≃ₜ (B ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (B ×ˢ I))
    (hσval : ∀ z : (B ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X))
    {t : ℝ} (ht : t ∈ I) :
    Nonempty (ChartwisePLSphere e (σ '' (B ×ˢ {t}))) := by
  have hpair : IsFinitePLBallPair P3 (halfBall 1) B := by
    rw [frontier_halfBall (Or.inl rfl)]
    exact isFinitePLBallPair_halfBall (Or.inl rfl)
  have hpairt := hpair.prod_singleton t
  obtain ⟨C,hC,hCb⟩ := hpairt.exists_cube_chart
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : P3 ≃L[ℝ] V3)
  have hCb' (x : (halfBall 1 ×ˢ {t} : Set (P3 × ℝ))) :
      (x : P3 × ℝ) ∈ B ×ˢ {t} ↔ (C x : V3) ∈ Sphere := by
    simpa only [frontier_closedBall _ one_ne_zero] using hCb x
  obtain ⟨KS,hKS,hKSs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  let Q := C.restrictSubsets hpairt.1 sphere_subset_closedBall hCb'
  have hQ : Q.IsFinitePL := hC.restrictSubsets_of_target
    hpairt.1 sphere_subset_closedBall hCb' KS hKS hKSs
  have hQcopy := hQ
  obtain ⟨_,⟨K,hK,hKs,_⟩,_⟩ := hQcopy
  change K.space = B ×ˢ {t} at hKs
  have hsub : B ×ˢ {t} ⊆ B ×ˢ I := prod_mono subset_rfl (singleton_subset_iff.mpr ht)
  have hg : PolyhedralPLInCharts e σ K.space :=
    hσ.restrict_finite K hK (hKs.subset.trans hsub)
  have hgi : InjOn σ K.space := by
    intro z hz w hw hzw
    have hz' := hsub (hKs.subset hz)
    have hw' := hsub (hKs.subset hw)
    have hh : H.symm ⟨z,hz'⟩ = H.symm ⟨w,hw'⟩ :=
      Subtype.ext ((hσval ⟨z,hz'⟩).symm.trans (hzw.trans (hσval ⟨w,hw'⟩)))
    exact congrArg Subtype.val (H.symm.injective hh)
  exact exists_chartwisePLSphere_image K hg hgi hKs.symm.subset Q hQ

theorem original_sphere_product_marked_endpoint
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U S : Set X}
    (H : U ≃ₜ (B ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (B ×ˢ I))
    (hσval : ∀ z : (B ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X))
    {t : ℝ} (ht : t ∈ I) (hSU : S ⊆ U)
    (hmark : ∀ x : U, (x : X) ∈ S ↔ (H x : P3 × ℝ).2 = t) :
    Nonempty (ChartwisePLSphere e S) := by
  have hS : S = σ '' (B ×ˢ {t}) := by
    apply Subset.antisymm
    · intro x hx
      let y : U := ⟨x,hSU hx⟩
      exact ⟨H y,⟨(H y).property.1,(hmark y).mp hx⟩,
        (hσval _).trans (congrArg Subtype.val (H.symm_apply_apply y))⟩
    · rintro _ ⟨z,hz,rfl⟩
      have hzt : z.2 = t := hz.2
      have hz' : z ∈ B ×ˢ I := ⟨hz.1,hzt.symm ▸ ht⟩
      have hh : (H (H.symm ⟨z,hz'⟩) : P3 × ℝ).2 = t := by
        rw [H.apply_symm_apply]
        exact hzt
      simpa only [hσval ⟨z,hz'⟩] using (hmark (H.symm ⟨z,hz'⟩)).mpr hh
  rw [hS]
  exact original_sphere_product_endpoint H σ hσ hσval ht

theorem original_sphere_product_plDomain
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X}
    (H : U ≃ₜ (B ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (B ×ˢ I))
    (hσval : ∀ z : (B ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source) :
    PLDomain e U := by
  obtain ⟨hU,_,hfront⟩ := original_sphere_product_frontier H σ hσ hσval
  have hreg := original_sphere_product_regularClosed H σ hσ hσval
  obtain ⟨s₀⟩ := original_sphere_product_endpoint H σ hσ hσval (show (0 : ℝ) ∈ I by norm_num)
  obtain ⟨s₁⟩ := original_sphere_product_endpoint H σ hσ hσval (show (1 : ℝ) ∈ I by norm_num)
  have hfront' : frontier U = (σ '' (B ×ˢ {(0 : ℝ)})) ∪ (σ '' (B ×ˢ {(1 : ℝ)})) := by
    rw [hfront,show ({0,1} : Set ℝ) = {0} ∪ {1} by ext; simp [or_comm],prod_union,image_union]
  have hdis : Disjoint (σ '' (B ×ˢ {(0 : ℝ)})) (σ '' (B ×ˢ {(1 : ℝ)})) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,hzx⟩ ⟨w,hw,hwx⟩
    have hz' : z ∈ B ×ˢ I := ⟨hz.1,by rw [show z.2 = 0 from hz.2]; norm_num⟩
    have hw' : w ∈ B ×ˢ I := ⟨hw.1,by rw [show w.2 = 1 from hw.2]; norm_num⟩
    have hh : H.symm ⟨z,hz'⟩ = H.symm ⟨w,hw'⟩ := Subtype.ext
      ((hσval ⟨z,hz'⟩).symm.trans (hzx.trans (hwx.symm.trans (hσval ⟨w,hw'⟩))))
    have hh' := congrArg (fun z : (B ×ˢ I : Set (P3 × ℝ)) => (z : P3 × ℝ).2)
      (H.symm.injective hh)
    have hz0 : z.2 = 0 := hz.2
    have hw1 : w.2 = 1 := hw.2
    dsimp at hh'
    linarith
  refine ⟨hcover,hcompat,hU.isClosed,?_⟩
  intro x hx
  rcases hfront'.subset hx with hx | hx
  · exact s₀.exists_regular_boundary_halfspace_chart hU.isClosed hreg s₁.isCompact.isClosed
      hcompat hcover (hfront'.trans (union_comm _ _)) hx
      (fun h => disjoint_left.mp hdis hx h)
  · exact s₁.exists_regular_boundary_halfspace_chart hU.isClosed hreg s₀.isCompact.isClosed
      hcompat hcover hfront' hx (fun h => disjoint_left.mp hdis h hx)

end PoincareConjecture.M76
