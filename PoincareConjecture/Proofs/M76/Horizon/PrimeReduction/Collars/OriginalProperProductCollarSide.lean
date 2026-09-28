import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.ProperProductCollarSide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalSphereBicollar

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1

theorem ChartwisePLSphere.exists_original_opposite_product_half_collar
    {X ι T : Type*} [MetricSpace X]
    [TopologicalSpace T] [CompactSpace T] [PreconnectedSpace T]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : P2 × T → X) (hj : Continuous (fun z : Disk × T => j (z.1,z.2)))
    (hproper : ∀ z ∈ Disk, ∀ t : T, j (z,t) ∈ S ↔ z ∈ Rim) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (N : SimplicialComplex ℝ (t → ℝ × V3))
      (HB : N.space ≃ₜ S) (c : (t → ℝ × V3) × ℝ → X)
      (ε : ℝ) (positive : Bool),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F R ∧ N.space = F '' S ∧
      N.faces.Finite ∧ PolyhedralPLInCharts e c (N.space ×ˢ I) ∧
      Topology.IsEmbedding (fun z : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)) => c z) ∧
      (∀ x : N.space, c ((x : t → ℝ × V3), 0) = HB x) ∧
      (∀ z : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)), c z ∈ S ↔ z.1.2 = 0) ∧
      0 < ε ∧ ε ≤ 1 / 4 ∧
      MapsTo c (N.space ×ˢ Icc (-ε) ε) (U ∩ interior R) ∧
      (∀ η : ℝ, 0 < η → η ≤ ε → IsOpen (c '' (N.space ×ˢ Ioo (-η) η))) ∧
      (c '' (N.space ×ˢ (if positive then Icc (-ε) 0 else Icc 0 ε))) ∩
        (j '' (Disk ×ˢ (univ : Set T))) = j '' (Rim ×ˢ (univ : Set T)) := by
  classical
  obtain ⟨t,F,N,HB,c,hFc,hF,hFi,hNF,hN,hc,hci,_,hc0,hcz,r,hr,hrhalf,hsmall,hopen⟩ :=
    s.exists_original_small_bicollar_with_model hR he hSR hU hSU
  let E := t → ℝ × V3
  let A := N.space
  let : CompactSpace A := isCompact_iff_compactSpace.mp (N.isCompact_space_of_finite hN)
  let f : A × I → X := fun z => c ((z.1 : E),r * (z.2 : ℝ))
  have hbound (z : A × I) : ((z.1 : E),r * (z.2 : ℝ)) ∈ N.space ×ˢ I := by
    refine ⟨z.1.property,?_,?_⟩ <;> nlinarith [z.2.property.1,z.2.property.2]
  have hfc : Continuous f := hc.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd))) hbound
  have hfi : Function.Injective f := by
    intro z w hzw
    have heq := congrArg Subtype.val (hci.injective
      (a₁ := ⟨_,hbound z⟩) (a₂ := ⟨_,hbound w⟩) hzw)
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst heq)
    · exact Subtype.ext (mul_left_cancel₀ hr.ne' (congrArg Prod.snd heq))
  let C := hfc.isClosedEmbedding hfi |>.isEmbedding.toHomeomorph
  let O := c '' (N.space ×ˢ Ioo (-r) r)
  have hOK : O ⊆ range f := by
    rintro _ ⟨⟨x,u⟩,⟨hx,hu⟩,rfl⟩
    have huI : u / r ∈ I := by
      constructor
      · apply (le_div_iff₀ hr).mpr
        linarith [hu.1]
      · apply (div_le_iff₀ hr).mpr
        linarith [hu.2]
    refine ⟨(⟨x,hx⟩,⟨u / r,huI⟩),?_⟩
    change c (x,r * (u / r)) = c (x,u)
    rw [mul_div_cancel₀ _ hr.ne']
  have hSO : S ⊆ O := by
    intro x hx
    refine ⟨((HB.symm ⟨x,hx⟩ : E),0),⟨(HB.symm ⟨x,hx⟩).property,by linarith,hr⟩,?_⟩
    rw [hc0]
    exact congrArg Subtype.val (HB.apply_symm_apply ⟨x,hx⟩)
  have hzero (z : A × I) : (C z : X) ∈ S ↔ (z.2 : ℝ) = 0 := by
    change c ((z.1 : E),r * (z.2 : ℝ)) ∈ S ↔ _
    rw [hcz ⟨_,hbound z⟩]
    exact mul_eq_zero.trans (or_iff_right hr.ne')
  obtain ⟨a,δ,positive,_,_,hδ,hδhalf,_,_,havoid⟩ :=
    exists_proper_product_opposite_collar_half C (hopen r hr le_rfl) hOK hSO hzero j hj hproper
  let ε := r * δ
  have hε : 0 < ε := mul_pos hr hδ
  have hεr : ε ≤ r := by dsimp [ε]; nlinarith
  have hεsmall : ε ≤ 1 / 4 := by dsimp [ε]; nlinarith
  have havoid' (z : E × ℝ) (hz : z.1 ∈ N.space)
      (ht : if positive then z.2 ∈ Ico (-ε) 0 else z.2 ∈ Ioc 0 ε) :
      c z ∉ j '' (Disk ×ˢ (univ : Set T)) := by
    have htime : |z.2| ≤ ε := by
      cases positive <;> simp only [Bool.false_eq_true,reduceIte] at ht ⊢ <;>
        exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have htI : z.2 / r ∈ I := by
      have hb := abs_le.mp htime
      constructor
      · apply (le_div_iff₀ hr).mpr
        linarith [hb.1]
      · apply (div_le_iff₀ hr).mpr
        linarith [hb.2]
    have hh := havoid (⟨z.1,hz⟩,⟨z.2 / r,htI⟩) (by
      cases positive <;> simp only [Bool.false_eq_true,reduceIte] at ht ⊢
      · exact ⟨div_pos ht.1 hr,(div_le_iff₀ hr).mpr (by nlinarith [ht.2])⟩
      · exact ⟨(le_div_iff₀ hr).mpr (by nlinarith [ht.1]),div_neg_of_neg_of_pos ht.2 hr⟩)
    change c (z.1,r * (z.2 / r)) ∉ j '' (Disk ×ˢ (univ : Set T)) at hh
    rwa [mul_div_cancel₀ _ hr.ne'] at hh
  refine ⟨t,F,N,HB,c,ε,positive,hFc,hF,hFi,hNF,hN,hc,hci,hc0,hcz,hε,hεsmall,?_,?_,?_⟩
  · exact hsmall.mono (prod_mono subset_rfl
      (Icc_subset_Icc (neg_le_neg hεr) hεr)) subset_rfl
  · intro η hη hηε
    exact hopen η hη (hηε.trans hεr)
  · apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hjx⟩
      have ht0 : z.2 = 0 := by
        by_contra ht0
        apply havoid' z hz.1 _ hjx
        cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hz ⊢
        · exact ⟨lt_of_le_of_ne hz.2.1 (Ne.symm ht0),hz.2.2⟩
        · exact ⟨hz.2.1,lt_of_le_of_ne hz.2.2 ht0⟩
      obtain ⟨⟨w,t⟩,⟨hw,ht⟩,hew⟩ := hjx
      refine ⟨(w,t),⟨(hproper w hw t).mp ?_,ht⟩,hew⟩
      have hzI : z ∈ N.space ×ˢ I := ⟨hz.1,by rw [ht0]; norm_num⟩
      exact hew ▸ (hcz ⟨z,hzI⟩).mpr ht0
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      have hzS := (hproper z (sphere_subset_closedBall hz) t).mpr hz
      refine ⟨?_,⟨(z,t),⟨sphere_subset_closedBall hz,ht⟩,rfl⟩⟩
      refine ⟨((HB.symm ⟨j (z,t),hzS⟩ : E),0),⟨(HB.symm ⟨j (z,t),hzS⟩).property,?_⟩,?_⟩
      · cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
          exact ⟨by linarith,by linarith⟩
      · rw [hc0]
        exact congrArg Subtype.val (HB.apply_symm_apply ⟨j (z,t),hzS⟩)

end PoincareConjecture.M76
