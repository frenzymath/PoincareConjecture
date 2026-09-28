import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentEmbedding









set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.three_lt_norm_lattice_vector
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι)
    {v : κ→ℝ} (hv : v∈L) (hv0 : v≠0) : 3 < ‖v‖ := by
  by_contra hn
  have hn := le_of_not_gt hn
  have hx : (1/2:ℝ) • v ∈ closedBall (0:κ→ℝ) (3/2) := by
    rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs]
    norm_num
    linarith
  have hy : -((1/2:ℝ) • v) ∈ closedBall (0:κ→ℝ) (3/2) := by
    simpa only [mem_closedBall_zero_iff,norm_neg] using hx
  have heq : (QuotientAddGroup.mk ((1/2:ℝ) • v) : (κ→ℝ) ⧸ L.toAddSubgroup) =
      QuotientAddGroup.mk (-((1/2:ℝ) • v)) := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hsub : (1/2:ℝ) • v - -((1/2:ℝ) • v) = v := by module
    rw [hsub]
    exact hv
  have hh := b.quotient_injOn_attaching_disk hpos hx hy heq
  have hz : v = 0 := by
    have hzero : (1/2:ℝ) • v + (1/2:ℝ) • v = 0 := eq_neg_iff_add_eq_zero.mp hh
    simpa [←add_smul] using hzero
  exact hv0 hz

theorem exists_shortest_nonzero_lattice_vector
    {κ : Type*} [Fintype κ] (L : Submodule ℤ (κ→ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (hk : 0 < Fintype.card κ) :
    ∃ v : κ→ℝ, v∈L ∧ v≠0 ∧ ∀ w : κ→ℝ, w∈L → w≠0 → ‖v‖≤‖w‖ := by
  classical
  let : Nonempty κ := Fintype.card_pos_iff.mp hk
  let j : κ := Classical.arbitrary κ
  let w : L := IsZLattice.basis L j
  have hw0 : (w:κ→ℝ) ≠ 0 := by
    intro hh
    exact (IsZLattice.basis L).ne_zero j (Subtype.ext hh)
  let S : Set (κ→ℝ) := (closedBall 0 ‖(w:κ→ℝ)‖ ∩ (L:Set (κ→ℝ))) \ {0}
  have hfinite : S.Finite := by
    apply Set.Finite.sdiff
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (isBounded_closedBall : Bornology.IsBounded (closedBall (0:κ→ℝ) ‖(w:κ→ℝ)‖))
      L.toAddSubgroup.isClosed_of_discrete
  obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S norm hfinite
    ⟨w,⟨⟨mem_closedBall_zero_iff.mpr le_rfl,w.property⟩,hw0⟩⟩
  refine ⟨v,hv.1.2,hv.2,?_⟩
  intro z hz hz0
  by_cases hzn : ‖z‖ ≤ ‖(w:κ→ℝ)‖
  · exact hmin z ⟨⟨mem_closedBall_zero_iff.mpr hzn,hz⟩,hz0⟩
  · exact (mem_closedBall_zero_iff.mp hv.1.1).trans (le_of_not_ge hzn)

theorem shortest_lattice_segment_avoids_translates
    {κ : Type*} [Fintype κ] (L : Submodule ℤ (κ→ℝ))
    {v : κ→ℝ} (hv : v∈L) (hv0 : v≠0)
    (hmin : ∀ w : κ→ℝ, w∈L → w≠0 → ‖v‖≤‖w‖)
    {r t : ℝ} (hr : 0<r) (_hvlen : 2*r < ‖v‖)
    (ht : r/‖v‖ ≤ t ∧ t ≤ 1-r/‖v‖) :
    ∀ w : κ→ℝ, w∈L → r ≤ ‖t • v-w‖ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have htr : r ≤ t*‖v‖ := (div_le_iff₀ hn).mp ht.1
  have htr' : r ≤ (1-t)*‖v‖ := by
    have hh := (div_le_iff₀ hn).mp (show r/‖v‖ ≤ 1-t by linarith)
    nlinarith
  have ht0 : 0 ≤ t := le_trans (div_pos hr hn).le ht.1
  have ht1 : t ≤ 1 := le_trans ht.2 (by linarith [div_pos hr hn])
  intro w hw
  by_cases hw0 : w=0
  · rw [hw0,sub_zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    exact htr
  by_cases hwv : w=v
  · have hsub : t • v-v=(t-1) • v := by module
    rw [hwv,hsub,norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    nlinarith
  have hwmin := hmin w hw hw0
  have hwm : v-w ∈ L := L.sub_mem hv hw
  have hwm0 : v-w ≠0 := sub_ne_zero.mpr (Ne.symm hwv)
  have hwmmin := hmin (v-w) hwm hwm0
  have hleft : ‖w‖ ≤ ‖t • v-w‖ + t*‖v‖ := by
    have hh := norm_sub_le (t • v) (t • v-w)
    simpa [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0,add_comm] using hh
  have hright : ‖v-w‖ ≤ ‖t • v-w‖ + (1-t)*‖v‖ := by
    have hh := norm_add_le (t • v-w) ((1-t) • v)
    have heq : (t • v-w) + (1-t) • v = v-w := by module
    rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith)] at hh
    exact hh
  linarith

theorem shortest_lattice_quotient_segment_injective
    {κ : Type*} [Fintype κ] (L : Submodule ℤ (κ→ℝ))
    {v : κ→ℝ} (hv0 : v≠0)
    (hmin : ∀ w : κ→ℝ, w∈L → w≠0 → ‖v‖≤‖w‖)
    {r : ℝ} (hr : 0<r) :
    InjOn (fun t:ℝ => (QuotientAddGroup.mk (t • v) : (κ→ℝ) ⧸ L.toAddSubgroup))
      (Icc (r/‖v‖) (1-r/‖v‖)) := by
  intro t ht u hu heq
  have hn : 0<‖v‖ := norm_pos_iff.mpr hv0
  have hw : t • v-u • v ∈ L := QuotientAddGroup.eq_iff_sub_mem.mp heq
  by_contra htu
  have hw0 : t • v-u • v ≠0 := by
    intro hh
    exact htu (smul_left_injective ℝ hv0 (sub_eq_zero.mp hh))
  have hmin' := hmin _ hw hw0
  rw [←sub_smul,norm_smul,Real.norm_eq_abs] at hmin'
  have htu' : |t-u|<1 := abs_lt.mpr (by
    have hh := div_pos hr hn
    constructor <;> linarith [ht.1,ht.2,hu.1,hu.2])
  nlinarith

theorem HamiltonMarkedProtectedBall.exists_marked_lattice_crossing_segment
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ v : κ→ℝ, v∈L ∧ v≠0 ∧ 3<‖v‖ ∧
      (∀ w : κ→ℝ, w∈L → w≠0 → ‖v‖≤‖w‖) ∧
      InjOn (fun t:ℝ => (QuotientAddGroup.mk (t • v) : (κ→ℝ) ⧸ L.toAddSubgroup))
        (Icc ((3/2)/‖v‖) (1-(3/2)/‖v‖)) ∧
      ∀ t∈Icc ((3/2)/‖v‖) (1-(3/2)/‖v‖),
        (QuotientAddGroup.mk (t • v) : (κ→ℝ) ⧸ L.toAddSubgroup) ∉
          (QuotientAddGroup.mk : (κ→ℝ) → (κ→ℝ) ⧸ L.toAddSubgroup) ''
            Metric.ball (0:κ→ℝ) (3/2) := by
  obtain ⟨v,hv,hv0,hmin⟩ := exists_shortest_nonzero_lattice_vector L (by omega)
  have hnorm := b.three_lt_norm_lattice_vector (by omega) hv hv0
  refine ⟨v,hv,hv0,hnorm,hmin,
    shortest_lattice_quotient_segment_injective L hv0 hmin (by norm_num),?_⟩
  intro t ht hbad
  obtain ⟨z,hz,hzeq⟩ := hbad
  have hw : t • v-z ∈ L := QuotientAddGroup.eq_iff_sub_mem.mp hzeq.symm
  have hh := shortest_lattice_segment_avoids_translates L hv hv0 hmin
    (r:=3/2) (by norm_num) (by linarith) ht _ hw
  have hznorm := mem_ball_zero_iff.mp hz
  simp only [sub_sub_cancel] at hh
  linarith

end PoincareConjecture.M76
