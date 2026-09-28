import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalLocalBoxGluing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalSpherePatchReplacement









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Box" => Set.prod Square (Icc (-1 : ℝ) 1)
local notation "Minus" => Set.prod Square (Icc (-1 : ℝ) 0)
local notation "Plus" => Set.prod Square (Icc (0 : ℝ) 1)
local notation "Base" => Set.prod Square ({0} : Set ℝ)



theorem ChartwisePLBall.patch_pair_chart_off_old_sphere
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q T S F A r : Set X}
    (b : ChartwisePLBall e Q T) (hSclosed : IsClosed S) (hAS : A ⊆ S)
    (H : OpenPartialHomeomorph X V3)
    (hH : ∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3)
    (L : V3 ≃L[ℝ] C3) {x : X} (hx : x ∈ H.source) (hHx : H x = 0)
    (hxS : x ∉ S)
    (hQ : ∀ y ∈ H.source,y ∈ Q ↔ (L (H y)).1.1 ≤ 0)
    (hF : ∀ y ∈ H.source,y ∈ F ↔ (L (H y)).2 = 0) :
    ∃ P : OpenPartialHomeomorph X V3,
      x ∈ P.source ∧ P x = 0 ∧ P.source ⊆ Sᶜ ∧
      (∀ i,(e i).symm.trans P ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ P.source,y ∈ (S \ (A \ r)) ∪ (T \ (A \ r)) ↔ P y 1 = 0) ∧
      ∀ y ∈ P.source,y ∈ F ↔ P y 0 = 0 := by
  let H0 := H.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hH0s : H0.source = H.source := by
    change H.source ∩ H ⁻¹' univ = H.source
    rw [preimage_univ,inter_univ]
  have hQi : H0.IsImage Q ((Iic (0 : ℝ) ×ˢ univ) ×ˢ univ) := by
    intro y hy
    change ((L (H y)).1.1 ∈ Iic 0 ∧ (L (H y)).1.2 ∈ univ) ∧ (L (H y)).2 ∈ univ ↔ y ∈ Q
    simpa only [mem_prod,mem_Iic,mem_univ,and_true] using (hQ y (hH0s.subset hy)).symm
  have hT (y : X) (hy : y ∈ H.source) : y ∈ T ↔ (L (H y)).1.1 = 0 := by
    have h := (hQi.frontier.apply_mem_iff (hH0s.symm.subset hy)).symm
    rw [b.frontier_eq,frontier_prod_univ_eq,frontier_prod_univ_eq,frontier_Iic] at h
    change y ∈ T ↔ ((L (H y)).1.1 ∈ ({0} : Set ℝ) ∧ (L (H y)).1.2 ∈ univ) ∧ (L (H y)).2 ∈ univ at h
    simpa only [mem_prod,mem_singleton_iff,mem_univ,and_true] using h
  let N : C3 ≃ₗ[ℝ] V3 := {
    toFun := fun z => ![z.2,z.1.1,z.1.2]
    invFun := fun z => ((z 1,z 2),z 0)
    map_add' := by intros; ext i; fin_cases i <;> rfl
    map_smul' := by intros; ext i; fin_cases i <;> rfl
    left_inv := by intro z; rfl
    right_inv := by intro z; ext i; fin_cases i <;> rfl }
  let M := L.trans N.toContinuousLinearEquiv
  let H1 := H.restrOpen Sᶜ hSclosed.isOpen_compl
  let P := H1.trans M.toHomeomorph.toOpenPartialHomeomorph
  have hPs : P.source = H.source ∩ Sᶜ := by
    change (H.source ∩ Sᶜ) ∩ H ⁻¹' univ = H.source ∩ Sᶜ
    rw [preimage_univ,inter_univ]
  have hM : M.toHomeomorph.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 :=
    ⟨locallyPiecewiseAffineOn_affine M.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine M.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ⟩
  refine ⟨P,hPs.symm.subset ⟨hx,hxS⟩,?_,fun y hy => (hPs.subset hy).2,?_,?_,?_⟩
  · change M (H x) = 0
    rw [hHx,map_zero]
  · intro i
    have hc := (e i).piecewiseAffine_compatible_restrOpen_right H (hH i) hSclosed.isOpen_compl
    simpa only [P,←OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans hc hM
  · intro y hy
    have hy' := hPs.subset hy
    have hlocal : y ∈ (S \ (A \ r)) ∪ (T \ (A \ r)) ↔ y ∈ T := by
      constructor
      · rintro (h | h)
        · exact (hy'.2 h.1).elim
        · exact h.1
      · exact fun h => Or.inr ⟨h,fun hn => hy'.2 (hAS hn.1)⟩
    exact hlocal.trans (hT y hy'.1)
  · intro y hy
    exact hF y (hPs.subset hy).1




theorem ChartwisePLBall.patch_pair_chart_of_glued_side_boxes
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q T S F A r E : Set X}
    (b : ChartwisePLBall e Q T) (hSclosed : IsClosed S) (hAS : A ⊆ S)
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {u v : C3 → X}
    (hu : PolyhedralPLInCharts e u Minus) (hui : InjOn u Minus)
    (hv : PolyhedralPLInCharts e v Plus) (hvi : InjOn v Plus)
    (huE : u '' Minus ⊆ E) (hvE : ∀ z ∈ Plus,v z ∈ E ↔ z.2 = 0)
    (huv : EqOn u v Base) (L : V3 ≃L[ℝ] C3) (hxS : u 0 ∉ S)
    (huMarks : ∀ z ∈ Minus,(u z ∈ Q ↔ z.1.1 ≤ 0) ∧ (u z ∈ F ↔ z.2 = 0))
    (hvMarks : ∀ z ∈ Plus,(v z ∈ Q ↔ z.1.1 ≤ 0) ∧ (v z ∈ F ↔ z.2 = 0)) :
    ∃ P : OpenPartialHomeomorph X V3,
      u 0 ∈ P.source ∧ P (u 0) = 0 ∧ P.source ⊆ Sᶜ ∧
      (∀ i,(e i).symm.trans P ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ P.source,y ∈ (S \ (A \ r)) ∪ (T \ (A \ r)) ↔ P y 1 = 0) ∧
      ∀ y ∈ P.source,y ∈ F ↔ P y 0 = 0 := by
  obtain ⟨f,H,_,_,hfu,hfv,hHs,_,_,hHf,hxH,hHx,hH⟩ :=
    exists_original_chart_of_glued_half_boxes he hu hui hv hvi huE hvE huv L
  have hmarks (z : C3) (hz : z ∈ Box) :
      (f z ∈ Q ↔ z.1.1 ≤ 0) ∧ (f z ∈ F ↔ z.2 = 0) := by
    by_cases ht : z.2 ≤ 0
    · have hzM : z ∈ Minus := ⟨hz.1,⟨hz.2.1,ht⟩⟩
      rw [hfu hzM]
      exact huMarks z hzM
    · have hzP : z ∈ Plus := ⟨hz.1,⟨(lt_of_not_ge ht).le,hz.2.2⟩⟩
      rw [hfv hzP]
      exact hvMarks z hzP
  have hvalues (y : X) (hy : y ∈ H.source) :
      (y ∈ Q ↔ (L (H y)).1.1 ≤ 0) ∧ (y ∈ F ↔ (L (H y)).2 = 0) := by
    obtain ⟨z,hz,rfl⟩ := hHs.subset hy
    rw [hHf z hz,L.apply_symm_apply]
    exact hmarks z (interior_subset hz)
  exact b.patch_pair_chart_off_old_sphere hSclosed hAS H hH L hxH hHx hxS
    (fun y hy => (hvalues y hy).1) (fun y hy => (hvalues y hy).2)

end PoincareConjecture.M76

