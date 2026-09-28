import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarPathSides

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76.PrismBelt

theorem exists_endpoint_neighborhood_collar_side
    {P X A : Type*} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace A]
    {S O K : Set X} (W : (A × unitInterval) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K)
    (hcenter : ∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (Γ : C(P × unitInterval,X))
    (haway : ∀ p (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → Γ (p,t) ∉ S)
    (p : P) (hzeroO : Γ (p,0) ∈ O) :
    ∃ (V : Set P) (ε : ℝ) (positive : Bool),
      IsOpen V ∧ p ∈ V ∧ 0 < ε ∧ ε ≤ 1/2 ∧
      (∀ q ∈ V, ∀ t : unitInterval, (t : ℝ) < ε → Γ (q,t) ∈ O) ∧
      ∀ q ∈ V, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < ε →
        ∀ z : A × unitInterval, (W z : X) = Γ (q,t) →
          if positive then 1/2 < (z.2 : ℝ) else (z.2 : ℝ) < 1/2 := by
  classical
  obtain ⟨u,j,hu,hj,hpu,h0j,hrect⟩ := isOpen_prod_iff.mp
    (hO.preimage Γ.continuous) p 0 hzeroO
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hj 0 h0j
  let ε := min r (1/2)
  have hε : 0 < ε := lt_min hr (by norm_num)
  have hεhalf : ε ≤ 1/2 := min_le_right _ _
  have hmaps (q : u) (t : unitInterval) (ht : (t : ℝ) < ε) : Γ (q,t) ∈ O := by
    apply hrect
    refine ⟨q.property,hball ?_⟩
    change dist (t : ℝ) 0 < r
    rw [Real.dist_eq,sub_zero,abs_of_nonneg t.property.1]
    exact ht.trans_le (min_le_left _ _)
  let T := Ioo (0 : ℝ) ε
  let time (t : T) : unitInterval :=
    ⟨t,t.property.1.le,t.property.2.le.trans (hεhalf.trans (by norm_num))⟩
  let lift (z : u × T) : K := ⟨Γ (z.1,time z.2),hOK (hmaps z.1 _ z.2.property.2)⟩
  have hlift : Continuous lift := (Γ.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _))).subtype_mk _
  let height (z : u × T) : ℝ := (W.symm (lift z)).2
  have hh : Continuous height :=
    continuous_subtype_val.comp (continuous_snd.comp (W.symm.continuous.comp hlift))
  have hne (q : u) (t : T) : height (q,t) ≠ 1/2 := by
    intro he
    have hs := (hcenter (W.symm (lift (q,t)))).mpr he
    rw [W.apply_symm_apply] at hs
    exact haway q (time t) t.property.1
      (t.property.2.trans_le (hεhalf.trans (by norm_num))) hs
  let t₀ : T := ⟨ε/2,by constructor <;> linarith⟩
  let positive : Bool := decide (1/2 < height (⟨p,hpu⟩,t₀))
  let U : Set u := {q | if positive then 1/2 < height (q,t₀) else height (q,t₀) < 1/2}
  have hU : IsOpen U := by
    have hc : Continuous (fun q : u => height (q,t₀)) := hh.comp (continuous_id.prodMk continuous_const)
    dsimp only [U]
    cases positive
    · exact isOpen_lt hc continuous_const
    · exact isOpen_lt continuous_const hc
  have hpU : (⟨p,hpu⟩ : u) ∈ U := by
    dsimp only [U,mem_ofPred_eq,positive]
    split_ifs with hp
    · exact of_decide_eq_true hp
    · have hn : ¬ 1/2 < height (⟨p,hpu⟩,t₀) := by simpa using hp
      exact lt_of_le_of_ne (le_of_not_gt hn) (hne _ _)
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hsign (q : u) (hq : q ∈ U) (t : T) :
      if positive then 1/2 < height (q,t) else height (q,t) < 1/2 := by
    have hc : Continuous (fun t : T => height (q,t)) := hh.comp (continuous_const.prodMk continuous_id)
    rcases isPreconnected_univ.mapsTo_Ioi_or_Iio hc.continuousOn (fun t _ => hne q t) with hp | hn
    · cases hpos : positive
      · have hqt : height (q,t₀) < 1/2 := by simpa [U,hpos] using hq
        exact (lt_asymm hqt (hp (mem_univ t₀))).elim
      · exact hp (mem_univ t)
    · cases hpos : positive
      · exact hn (mem_univ t)
      · have hqt : 1/2 < height (q,t₀) := by simpa [U,hpos] using hq
        exact (lt_asymm hqt (hn (mem_univ t₀))).elim
  refine ⟨Subtype.val '' U,ε,positive,hu.isOpenMap_subtype_val U hU,
    ⟨⟨p,hpu⟩,hpU,rfl⟩,hε,hεhalf,?_,?_⟩
  · rintro q ⟨q,hq,rfl⟩ t ht
    exact hmaps q t ht
  · rintro q ⟨q,hq,rfl⟩ t ht hte z hz
    let v : T := ⟨t,ht,hte⟩
    have hv : W z = lift (q,v) := Subtype.ext hz
    have hsymm : W.symm (lift (q,v)) = z := by rw [← hv,W.symm_apply_apply]
    simpa only [height,hsymm] using hsign q hq v

end PoincareConjecture.M76.PrismBelt
