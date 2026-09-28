import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawCenteredProductCollar
import Mathlib.Topology.Connected.LocallyPathConnected



set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76.PrismBelt

theorem exists_endpoint_path_collar_side
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    {S O K : Set X} (W : (A × unitInterval) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hSO : S ⊆ O)
    (hcenter : ∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (γ : C(unitInterval,X)) (hγzero : γ 0 ∈ S)
    (hγaway : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∉ S) :
    ∃ (ε : ℝ) (positive : Bool), 0 < ε ∧ ε ≤ 1/2 ∧
      (∀ t : unitInterval, (t : ℝ) < ε → γ t ∈ O) ∧
      ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < ε →
        ∀ z : A × unitInterval, (W z : X) = γ t →
          if positive then 1/2 < (z.2 : ℝ) else (z.2 : ℝ) < 1/2 := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (hO.preimage γ.continuous) 0 (hSO hγzero)
  let ε := min r (1/2)
  have hε : 0 < ε := lt_min hr (by norm_num)
  have hεhalf : ε ≤ 1/2 := min_le_right _ _
  have hmaps (t : unitInterval) (ht : (t : ℝ) < ε) : γ t ∈ O := by
    apply hball
    change dist (t : ℝ) 0 < r
    rw [Real.dist_eq,sub_zero,abs_of_nonneg t.property.1]
    exact ht.trans_le (min_le_left _ _)
  let u (t : Ioo (0 : ℝ) ε) : unitInterval := ⟨t,t.property.1.le,
    t.property.2.le.trans (hεhalf.trans (by norm_num))⟩
  let lift (t : Ioo (0 : ℝ) ε) : K := ⟨γ (u t),hOK (hmaps (u t) t.property.2)⟩
  have hlift : Continuous lift :=
    (γ.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  let height (t : Ioo (0 : ℝ) ε) : ℝ := (W.symm (lift t)).2
  have hh : Continuous height :=
    continuous_subtype_val.comp (continuous_snd.comp (W.symm.continuous.comp hlift))
  have hne (t : Ioo (0 : ℝ) ε) : height t ≠ 1/2 := by
    intro he
    have hS := (hcenter (W.symm (lift t))).mpr he
    rw [W.apply_symm_apply] at hS
    exact hγaway (u t) t.property.1 (t.property.2.trans_le
      (hεhalf.trans (by norm_num))) hS
  let : PreconnectedSpace (Ioo (0 : ℝ) ε) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  obtain ⟨positive,hpositive⟩ : ∃ positive : Bool, ∀ t : Ioo (0 : ℝ) ε,
      if positive then 1/2 < height t else height t < 1/2 := by
    rcases isPreconnected_univ.mapsTo_Ioi_or_Iio hh.continuousOn (fun t _ => hne t) with hp | hn
    · exact ⟨true,fun t => hp (mem_univ t)⟩
    · exact ⟨false,fun t => hn (mem_univ t)⟩
  refine ⟨ε,positive,hε,hεhalf,hmaps,?_⟩
  intro t ht hte z hz
  let v : Ioo (0 : ℝ) ε := ⟨t,ht,hte⟩
  have hv : W z = lift v := Subtype.ext hz
  have hsymm : W.symm (lift v) = z := by rw [← hv,W.symm_apply_apply]
  simpa only [height,hsymm] using hpositive v

end PoincareConjecture.M76.PrismBelt
