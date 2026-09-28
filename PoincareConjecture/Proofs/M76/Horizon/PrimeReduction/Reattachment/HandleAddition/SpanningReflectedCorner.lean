import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Reflection.OpenChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCornerPairCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem doubleHalfspaceMap_zero_iff
    {f : C3 → C3} {A : Set P2} {r : ℝ}
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r,(f z).2 = 0 ↔ z.2 = 0)
    {z : C3} (hz : z ∈ A ×ˢ Icc (-r) r) :
    (doubleHalfspaceMap f z).2 = 0 ↔ z.2 = 0 := by
  by_cases hn : 0 ≤ z.2
  · rw [doubleHalfspaceMap_positive f hn]
    exact hfzero z ⟨hz.1,hn,hz.2.2⟩
  · have hneg : z ∈ A ×ˢ Icc (-r) 0 := ⟨hz.1,hz.2.1,(lt_of_not_ge hn).le⟩
    have href : collarNormalReflection z ∈ A ×ˢ Icc (0 : ℝ) r :=
      ⟨hz.1,by change 0 ≤ -z.2; linarith,by change -z.2 ≤ r; linarith [hz.2.1]⟩
    rw [doubleHalfspaceMap_negative hfzero hneg]
    change -(f (collarNormalReflection z)).2 = 0 ↔ z.2 = 0
    rw [neg_eq_zero,hfzero _ href]
    change -z.2 = 0 ↔ z.2 = 0
    exact neg_eq_zero

theorem doubleHalfspaceMap_transverse_zero_iff
    {f : C3 → C3} {A : Set P2} {r : ℝ}
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r,(f z).2 = 0 ↔ z.2 = 0)
    (hftrans : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r,(f z).1.1 = 0 ↔ z.1.1 = 0)
    {z : C3} (hz : z ∈ A ×ˢ Icc (-r) r) :
    (doubleHalfspaceMap f z).1.1 = 0 ↔ z.1.1 = 0 := by
  by_cases hn : 0 ≤ z.2
  · rw [doubleHalfspaceMap_positive f hn]
    exact hftrans z ⟨hz.1,hn,hz.2.2⟩
  · have hneg : z ∈ A ×ˢ Icc (-r) 0 := ⟨hz.1,hz.2.1,(lt_of_not_ge hn).le⟩
    have href : collarNormalReflection z ∈ A ×ˢ Icc (0 : ℝ) r :=
      ⟨hz.1,by change 0 ≤ -z.2; linarith,by change -z.2 ≤ r; linarith [hz.2.1]⟩
    rw [doubleHalfspaceMap_negative hfzero hneg]
    exact hftrans _ href

private def reflectedCornerCoordinates : C3 ≃L[ℝ] C3 where
  toFun z := ((-z.2,z.1.2),z.1.1)
  invFun z := ((z.2,z.1.2),-z.1.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp [add_comm]
  map_smul' c z := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem exists_original_corner_chart_from_halfspace
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S W Q F : Set X} {x : X}
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (L : V3 ≃L[ℝ] C3) (hxB : x ∈ B.source) (hBx : B x = 0)
    (hQW : Q ⊆ W)
    (hW : ∀ z ∈ B.target,B.symm z ∈ W ↔ 0 ≤ (L z).2)
    (hS : ∀ z ∈ B.target,B.symm z ∈ S ↔ (L z).2 = 0)
    (hF : ∀ z ∈ B.target,B.symm z ∈ F ↔ (L z).1.1 = 0)
    {A : Set P2} {r : ℝ} (hr : 0 < r) (hA : (0 : P2) ∈ interior A)
    (f : C3 → C3) (hf : FinitePiecewiseAffineOn f (A ×ˢ Icc (0 : ℝ) r))
    (hfi : InjOn f (A ×ˢ Icc (0 : ℝ) r)) (hf0 : f 0 = 0)
    (hfpos : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r,0 ≤ (f z).2)
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r,(f z).2 = 0 ↔ z.2 = 0)
    (hftrans : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r,(f z).1.1 = 0 ↔ z.1.1 = 0)
    (hfQ : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r,B.symm (L.symm (f z)) ∈ Q ↔ z.1.2 ≤ 0) :
    ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ (L (H y)).1.1 = 0) ∧
      (∀ y ∈ H.source,y ∈ Q ↔ (L (H y)).1.1 ≤ 0 ∧ (L (H y)).1.2 ≤ 0) ∧
      ∀ y ∈ H.source,y ∈ F ↔ (L (H y)).2 = 0 := by
  obtain ⟨D,hDs,hD0,hDz,hD,hDi,hDf,hDhalf,hDpos⟩ :=
    exists_doubled_halfspace_open_chart hr hA hf hfi hf0 hfpos hfzero
  let N := (L.toHomeomorph.toOpenPartialHomeomorph.trans D.symm).trans
    (reflectedCornerCoordinates.toHomeomorph.trans L.symm.toHomeomorph).toOpenPartialHomeomorph
  let H := B.trans N
  have hL (y : X) : L (H y) = reflectedCornerCoordinates (D.symm (L (B y))) :=
    L.apply_symm_apply _
  have htarget {y : X} (hy : y ∈ H.source) : L (B y) ∈ D.target := hy.2.1.2
  have hsource {y : X} (hy : y ∈ H.source) : D.symm (L (B y)) ∈ D.source :=
    D.map_target (htarget hy)
  have hzeroD : D.symm 0 = 0 :=
    (congrArg D.symm hDz.symm).trans (D.left_inv hD0)
  have hNPL : N ∈ piecewiseAffineGroupoid V3 := by
    have hLP := locallyPiecewiseAffineOn_affine L.toContinuousLinearMap.toContinuousAffineMap isOpen_univ
    have hTP := locallyPiecewiseAffineOn_affine
      (L.symm.toContinuousLinearMap.comp reflectedCornerCoordinates.toContinuousLinearMap).toContinuousAffineMap
      isOpen_univ
    have hNP : LocallyPiecewiseAffineOn N N.source := by
      change LocallyPiecewiseAffineOn (fun z => L.symm (reflectedCornerCoordinates (D.symm (L z))))
        ((univ ∩ L ⁻¹' D.target) ∩ (fun z => D.symm (L z)) ⁻¹' univ)
      simpa [Function.comp_def] using hTP.comp (hDi.comp hLP)
    exact ⟨hNP,N.locallyPiecewiseAffineOn_symm hNP⟩
  refine ⟨H,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨hxB,⟨mem_univ _,?_⟩,mem_univ _⟩
    change L (B x) ∈ D.target
    rw [hBx,map_zero,←hDz]
    exact D.map_source hD0
  · apply L.injective
    rw [hL,hBx,map_zero,hzeroD,map_zero]
  · intro i
    simpa only [H,←OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans (hB i) hNPL
  · intro y hy
    have hz := doubleHalfspaceMap_zero_iff hfzero (interior_subset (hDs.subset (hsource hy)))
    rw [←hDf,D.right_inv (htarget hy)] at hz
    have hSy : y ∈ S ↔ (L (B y)).2 = 0 := by
      simpa only [B.left_inv hy.1] using hS (B y) (B.map_source hy.1)
    rw [hSy]
    rw [hL]
    change (L (B y)).2 = 0 ↔ -(D.symm (L (B y))).2 = 0
    exact hz.trans neg_eq_zero.symm
  · intro y hy
    have hhalf := hDhalf _ (hsource hy)
    rw [D.right_inv (htarget hy)] at hhalf
    have hwy : y ∈ W ↔ 0 ≤ (D.symm (L (B y))).2 := by
      rw [←B.left_inv hy.1,hW _ (B.map_source hy.1),B.right_inv (B.map_source hy.1)]
      exact hhalf
    have hparam (hn : 0 ≤ (D.symm (L (B y))).2) :
        D.symm (L (B y)) ∈ A ×ˢ Icc (0 : ℝ) r ∧
        f (D.symm (L (B y))) = L (B y) := by
      have hm := interior_subset (hDs.subset (hsource hy))
      exact ⟨⟨hm.1,hn,hm.2.2⟩,(hDpos _ (hsource hy) hn).symm.trans (D.right_inv (htarget hy))⟩
    rw [hL]
    change y ∈ Q ↔ -(D.symm (L (B y))).2 ≤ 0 ∧ (D.symm (L (B y))).1.2 ≤ 0
    constructor
    · intro hyQ
      have hn := hwy.mp (hQW hyQ)
      obtain ⟨hm,hfv⟩ := hparam hn
      have hq := hfQ _ hm
      rw [hfv,L.symm_apply_apply,B.left_inv hy.1] at hq
      exact ⟨by linarith,hq.mp hyQ⟩
    · rintro ⟨hn,hq⟩
      obtain ⟨hm,hfv⟩ := hparam (by linarith)
      have hq' := (hfQ _ hm).mpr hq
      simpa only [hfv,L.symm_apply_apply,B.left_inv hy.1] using hq'
  · intro y hy
    have hz := doubleHalfspaceMap_transverse_zero_iff hfzero hftrans
      (interior_subset (hDs.subset (hsource hy)))
    rw [←hDf,D.right_inv (htarget hy)] at hz
    have hFy : y ∈ F ↔ (L (B y)).1.1 = 0 := by
      simpa only [B.left_inv hy.1] using hF (B y) (B.map_source hy.1)
    rw [hFy]
    rw [hL]
    exact hz

theorem exists_original_corner_chart_of_marked_sector
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S W Q F : Set X} {x : X}
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (L : V3 ≃L[ℝ] C3) (hxB : x ∈ B.source) (hBx : B x = 0)
    (hQW : Q ⊆ W)
    (hW : ∀ z ∈ B.target,B.symm z ∈ W ↔ 0 ≤ (L z).2)
    (hS : ∀ z ∈ B.target,B.symm z ∈ S ↔ (L z).2 = 0)
    (hF : ∀ z ∈ B.target,B.symm z ∈ F ↔ (L z).1.1 = 0)
    (g : C3 → X)
    (hg : PolyhedralPLInCharts e g ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1))
    (hg0 : g 0 = x)
    (hgB : MapsTo g ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) B.source)
    (hgW : MapsTo g ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) W)
    (hgmarks : ∀ z ∈ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1,
      (g z ∈ S ↔ z.2 = 0) ∧ (g z ∈ F ↔ z.1.1 = 0) ∧ (g z ∈ Q ↔ z.1.2 ≤ 0)) :
    ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ (L (H y)).1.1 = 0) ∧
      (∀ y ∈ H.source,y ∈ Q ↔ (L (H y)).1.1 ≤ 0 ∧ (L (H y)).1.2 ≤ 0) ∧
      ∀ y ∈ H.source,y ∈ F ↔ (L (H y)).2 = 0 := by
  let A := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  let T := A ×ˢ Icc (0 : ℝ) 1
  have hi := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have ht := (hi.prod hi).prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKT,_⟩,_⟩,_⟩ := ht
  change K.space = T at hKT
  change PolyhedralPLInCharts e g T at hg
  have hcoords := (hKT.symm ▸ hg).finitePiecewiseAffineOn_compatible_chart_finite_source
    K hK B hB (fun z hz => hgB (hKT.subset hz))
  let f : C3 → C3 := L ∘ B ∘ g
  have hf : FinitePiecewiseAffineOn f T :=
    hKT ▸ hcoords.postcomp L.toContinuousLinearMap.toContinuousAffineMap
  have hfi : InjOn f T := by
    intro z hz w hw hzw
    exact hgi hz hw (B.injOn (hgB hz) (hgB hw) (L.injective hzw))
  have hf0 : f 0 = 0 := by change L (B (g 0)) = 0; rw [hg0,hBx,map_zero]
  have hfpos : ∀ z ∈ T,0 ≤ (f z).2 := by
    intro z hz
    apply (hW _ (B.map_source (hgB hz))).mp
    rw [B.left_inv (hgB hz)]
    exact hgW hz
  have hfzero : ∀ z ∈ T,(f z).2 = 0 ↔ z.2 = 0 := by
    intro z hz
    change (L (B (g z))).2 = 0 ↔ z.2 = 0
    rw [←hS _ (B.map_source (hgB hz)),B.left_inv (hgB hz)]
    exact (hgmarks z hz).1
  have hftrans : ∀ z ∈ T,(f z).1.1 = 0 ↔ z.1.1 = 0 := by
    intro z hz
    change (L (B (g z))).1.1 = 0 ↔ z.1.1 = 0
    rw [←hF _ (B.map_source (hgB hz)),B.left_inv (hgB hz)]
    exact (hgmarks z hz).2.1
  have hfQ : ∀ z ∈ T,B.symm (L.symm (f z)) ∈ Q ↔ z.1.2 ≤ 0 := by
    intro z hz
    change B.symm (L.symm (L (B (g z)))) ∈ Q ↔ z.1.2 ≤ 0
    rw [L.symm_apply_apply,B.left_inv (hgB hz)]
    exact (hgmarks z hz).2.2
  exact exists_original_corner_chart_from_halfspace B hB L hxB hBx hQW hW hS hF
    (by norm_num : (0 : ℝ) < 1) (by
      change (0 : P2) ∈ interior (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      rw [interior_prod_eq,interior_Icc]
      norm_num)
    f hf hfi hf0 hfpos hfzero hftrans hfQ

end PoincareConjecture.M76
