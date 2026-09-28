import PoincareConjecture.Proofs.M33.GuardedCylinders
import PoincareConjecture.Proofs.M12.GeneralizedRicci










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



def surgeryCapExcludedSlice (F : SurgeryFlowData.{u}) (t : ℝ)
    (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier] (R : ℝ) :
    Set (F.slice t).carrier :=
  (⋃ i : Fin (F.event t hT).cap_count,
    (F.metric t).ball ((F.event t hT).caps i).tip (R * F.parameters.h t))ᶜ




theorem surgeryCapExcludedSlice_compact_regular
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] {R : ℝ}
    (hR : F.standard_initial.cylindrical_end.radius + 5 < R) :
    IsCompact (surgeryCapExcludedSlice F t hT R) ∧
      surgeryCapExcludedSlice F t hT R ⊆ m33RegularRegion F t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : EMetricSpace (F.slice t).carrier := .ofRiemannianMetric (𝓡 3) (F.slice t).carrier
  have hopen : IsOpen (⋃ i : Fin (F.event t hT).cap_count,
      (F.metric t).ball ((F.event t hT).caps i).tip (R * F.parameters.h t)) := by
    apply isOpen_iUnion
    intro i
    change IsOpen {x | edist ((F.event t hT).caps i).tip x <
      ENNReal.ofReal (R * F.parameters.h t)}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hcompact : IsCompact (surgeryCapExcludedSlice F t hT R) :=
    (F.slices_compact t (F.surgery_times_subset hT)).of_isClosed_subset
      hopen.isClosed_compl (subset_univ _)
  refine ⟨hcompact, ?_⟩
  intro x hx hT'
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hRpos : 0 < R := by linarith [F.standard_initial.cylindrical_end.radius_pos]
  have hnocap : x ∉ ⋃ i : Fin (F.event t hT).cap_count, ((F.event t hT).caps i).carrier := by
    intro hcap
    obtain ⟨i, hi⟩ := mem_iUnion.mp hcap
    have houter := ((F.event t hT).caps i).outer_ball hi
    apply hx
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change (F.metric t).edist ((F.event t hT).caps i).tip x <
      ENNReal.ofReal (R * F.parameters.h t)
    apply houter.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hRpos hh)).mpr
    nlinarith
  have hclosed : IsClosed
      (⋃ i : Fin (F.event t hT).cap_count, ((F.event t hT).caps i).carrier) :=
    isClosed_iUnion_of_finite (fun i => ((F.event t hT).caps i).carrier_compact.isClosed)
  have hret : (⋃ i : Fin (F.event t hT).cap_count, ((F.event t hT).caps i).carrier)ᶜ ⊆
      (F.event t hT).retained_post := by
    intro z hz
    have hcover : z ∈ (F.event t hT).retained_post ∪
        ⋃ i : Fin (F.event t hT).cap_count, ((F.event t hT).caps i).carrier := by
      rw [(F.event t hT).post_cover]
      exact mem_univ z
    exact hcover.resolve_right hz
  apply interior_mono hret
  rw [hclosed.isOpen_compl.interior_eq]
  exact hnocap




theorem regularSliceLift_compact
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
    {K : Set (F.slice t).carrier} (hK : IsCompact K)
    (hregular : K ⊆ m33RegularRegion F t) :
    IsCompact ((fun x => (⟨t, H.history.inverse t ht x⟩ : H.generalized.point)) '' K) ∧
      ∀ y : (H.generalized.slice t).carrier, H.history.forward t ht y ∈ K →
        (⟨t, y⟩ : H.generalized.point) ∈
          (fun x => (⟨t, H.history.inverse t ht x⟩ : H.generalized.point)) '' K := by
  have hrange : K ⊆ range (H.history.forward t ht) := by
    rwa [H.regular_range t ht]
  have hcont : ContinuousOn (fun x =>
      (⟨t, H.history.inverse t ht x⟩ : H.generalized.point)) K :=
    (H.generalized.slice_embedding t).continuous.comp_continuousOn
      ((H.history.inverse_smooth t ht).continuousOn.mono hrange)
  refine ⟨hK.image_of_continuousOn hcont, ?_⟩
  intro y hy
  refine ⟨H.history.forward t ht y, hy, ?_⟩
  dsimp only
  rw [H.history.left_inverse t ht y]

end PoincareConjecture.Proofs.M46
