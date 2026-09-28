import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.CapAttachmentPointCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FiniteCapChartExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FiniteCapInteriorCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.OriginalModelInteriorBalls










set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

private theorem exists_extended_finitePL_point_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T W C A : Set E} (q : OpenPartialHomeomorph T V3)
    (hTW : T ⊆ W) (hcover : W ⊆ T ∪ C) (hC : IsClosed C)
    (p : T) (hp : p ∈ q.source) (hpC : (p : E) ∉ C)
    {a : E → V3} {b : V3 → E}
    (ha : FinitePiecewiseAffineOn a A)
    (hb : FinitePiecewiseAffineOn b (closedBall (0 : V3) 1))
    (hqs : ∀ x ∈ q.source, (x : E) ∈ A)
    (hqt : q.target ⊆ interior (closedBall (0 : V3) 1))
    (hqa : ∀ x ∈ q.source, q x = a x)
    (hqb : ∀ y ∈ q.target, (q.symm y : E) = b y) :
    ∃ Q : OpenPartialHomeomorph W V3,
      (⟨p, hTW p.property⟩ : W) ∈ Q.source ∧
      (∀ x ∈ Q.source, (x : E) ∈ A) ∧
      Q.target ⊆ interior (closedBall (0 : V3) 1) ∧
      FinitePiecewiseAffineOn a A ∧
      FinitePiecewiseAffineOn b (closedBall (0 : V3) 1) ∧
      (∀ x ∈ Q.source, Q x = a x) ∧
      ∀ y ∈ Q.target, (Q.symm y : E) = b y := by
  obtain ⟨Q, hQs, hQt, hpQ, hQq, hQinv⟩ :=
    q.exists_extension_away_from_closed hTW hcover hC p hp hpC
  refine ⟨Q, hpQ, ?_, ?_, ha, hb, ?_, ?_⟩
  · intro x hx
    rw [hQs] at hx
    obtain ⟨z, hz, hzx⟩ := hx.1
    exact hzx ▸ hqs z hz
  · rw [hQt]
    exact fun _ hy => hqt hy.1
  · intro x hx
    rw [hQs] at hx
    obtain ⟨z, hz, hzx⟩ := hx.1
    calc
      Q x = Q ⟨z, hTW z.property⟩ := congrArg Q (Subtype.ext hzx.symm)
      _ = q z := hQq z
      _ = a z := hqa z hz
      _ = a x := congrArg a hzx
  · intro y hy
    rw [hQinv]
    exact hqb y ((hQt ▸ hy).1)



theorem exists_finite_capped_carrier_point_chart
    {X E ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {P Z : Set E}
    (he : PLDomain e R) (f : X → E)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hfi : InjOn f R) (H : R ≃ₜ P) (hH : ∀ x : R, (H x : E) = f x)
    (hP : IsClosed P) (D B : κ → Set E)
    (hclosed : ∀ i, IsClosed (D i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hball : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hattach : ∀ i, P ∩ D i = B i)
    (hboundary : f '' frontier R ⊆ Z ∪ ⋃ i, B i)
    (hcollar : ∀ i, ∃ (c : E × ℝ → E)
      (C : (B i ×ˢ I : Set (E × ℝ)) ≃ₜ c '' (B i ×ˢ I)),
      C.IsFinitePL ∧ (∀ z, (C z : E) = c z) ∧ MapsTo c (B i ×ˢ I) P ∧
      (∀ x ∈ B i, c (x, 0) = x) ∧
      (∀ z ∈ B i ×ˢ I, c z ∈ B i ↔ z.2 = 0) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        IsOpen ((Subtype.val : P → E) ⁻¹' (c '' (B i ×ˢ Ico 0 ε))))
    (p : (P ∪ ⋃ i, D i : Set E)) (hpZ : (p : E) ∉ Z) :
    ∃ (A : Set E) (Q : OpenPartialHomeomorph (P ∪ ⋃ i, D i : Set E) V3)
      (a : E → V3) (b : V3 → E),
      A ⊆ P ∪ ⋃ i, D i ∧ p ∈ Q.source ∧
      (∀ x ∈ Q.source, (x : E) ∈ A) ∧
      Q.target ⊆ interior (closedBall (0 : V3) 1) ∧
      FinitePiecewiseAffineOn a A ∧
      FinitePiecewiseAffineOn b (closedBall (0 : V3) 1) ∧
      (∀ x ∈ Q.source, Q x = a x) ∧
      ∀ y ∈ Q.target, (Q.symm y : E) = b y := by
  classical
  by_cases hpCaps : (p : E) ∈ ⋃ i, D i
  · obtain ⟨i, hpi⟩ := mem_iUnion.mp hpCaps
    by_cases hpB : (p : E) ∈ B i
    · obtain ⟨c, C, hC, hCval, hcP, hc0, hcB, hopen⟩ := hcollar i
      obtain ⟨A, rim, hAT, q, a, b, _, hpA, hqs, hqt, ha, hb, hqa, hqb, _⟩ :=
        (hball i).exists_attachment_point_chart hP (hattach i) c C hC hCval
          hcP hc0 hcB (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hopen hpB
      let others := ⋃ j : {j // j ≠ i}, D j
      have hothers : IsClosed others := isClosed_iUnion_of_finite (fun j => hclosed j)
      have hpOther : (p : E) ∉ others := by
        intro hpO
        obtain ⟨j, hj⟩ := mem_iUnion.mp hpO
        exact disjoint_left.mp (hdis j.property.symm) hpi hj
      have hTW : P ∪ D i ⊆ P ∪ ⋃ j, D j := by
        intro x hx
        exact hx.elim Or.inl (fun hi => Or.inr (mem_iUnion.mpr ⟨i, hi⟩))
      have hcover : (P ∪ ⋃ j, D j) ⊆ (P ∪ D i) ∪ others := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
          by_cases hji : j = i
          · exact Or.inl (Or.inr (hji ▸ hj))
          · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
      let pT : (P ∪ D i : Set E) := ⟨p, Or.inr hpi⟩
      have hpq : pT ∈ q.source := hqs.symm ▸ hpA
      obtain ⟨Q, hpQ, hsA, ht, ha, hb, hQa, hQb⟩ :=
        exists_extended_finitePL_point_chart q hTW hcover hothers pT hpq hpOther ha hb
          (fun x hx => (hqs ▸ hx).1) (hqt ▸ subset_rfl)
          (fun x _ => hqa x) (fun y hy => hqb y (interior_subset (hqt ▸ hy)))
      exact ⟨A, Q, a, b, hAT.trans hTW, hpQ, hsA, ht, ha, hb, hQa, hQb⟩
    · have hDiP : D i ∩ P = B i := (inter_comm _ _).trans (hattach i)
      obtain ⟨Q, a, b, hQs, hQt, hpQ, ha, hb, hQa, hQb, _⟩ :=
        (hball i).exists_finite_cap_interior_chart P D hP hclosed hdis i hDiP
          (ContinuousLinearEquiv.refl ℝ V3) ⟨hpi, hpB⟩
      refine ⟨D i, Q, a, b, fun _ hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩),
        hpQ, (fun x hx => (hQs ▸ hx).1), hQt ▸ subset_rfl, ha, hb,
        (fun x _ => hQa x), fun y hy => hQb y (interior_subset (hQt ▸ hy))⟩
  · have hpP : (p : E) ∈ P := p.property.resolve_right hpCaps
    let pP : P := ⟨p, hpP⟩
    let x : R := H.symm pP
    have hfx : f x = (p : E) :=
      (hH x).symm.trans (congrArg Subtype.val (H.apply_symm_apply pP))
    have hxInt : (x : X) ∈ interior R := by
      apply (mem_interior_iff_notMem_frontier x.property).mpr
      intro hxFr
      rcases hboundary ⟨x, hxFr, hfx⟩ with hz | hb
      · exact hpZ hz
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hb
        exact hpCaps (mem_iUnion.mpr ⟨i, (hball i).1 hi⟩)
    obtain ⟨A, rim, q, a, b, _, _, hAP, hpq, hqs, hqt, ha, hb, hqa, hqb, _⟩ :=
      exists_original_model_interior_chart he f hf hfi H hH isOpen_univ
        (show (x : X) ∈ univ ∩ interior R from ⟨mem_univ _, hxInt⟩)
    have hpq' : pP ∈ q.source := by
      simpa only [x, H.apply_symm_apply] using hpq
    have hPW : P ⊆ P ∪ ⋃ i, D i := subset_union_left
    obtain ⟨Q, hpQ, hsA, ht, ha, hb, hQa, hQb⟩ :=
      exists_extended_finitePL_point_chart q hPW subset_rfl
        (isClosed_iUnion_of_finite hclosed) pP hpq' hpCaps ha hb
        (fun y hy => (hqs ▸ hy).1) (hqt ▸ subset_rfl)
        (fun y _ => hqa y) (fun y hy => hqb y (interior_subset (hqt ▸ hy)))
    exact ⟨A, Q, a, b, hAP.trans hPW, hpQ, hsA, ht, ha, hb, hQa, hQb⟩

end PoincareConjecture.M76
