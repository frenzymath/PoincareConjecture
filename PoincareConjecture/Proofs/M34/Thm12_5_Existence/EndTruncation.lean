import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.EndCoordinates
import PoincareConjecture.Proofs.M09.RiemannianProper

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

def endClosedTail (e : StandardCylindricalEnd g) (L : ℝ) : Set StandardCapSpace :=
  e.coordinate '' (univ ×ˢ Ici L)

def endTruncation (e : StandardCylindricalEnd g) (L : ℝ) : Set StandardCapSpace :=
  (endClosedTail e L)ᶜ

def endTruncatedCore (e : StandardCylindricalEnd g) (L : ℝ) : Set StandardCapSpace :=
  (e.coordinate '' (univ ×ˢ Ioi L))ᶜ

theorem end_carrier_isClosed (e : StandardCylindricalEnd g) : IsClosed e.carrier := by
  let : MetricSpace StandardCapSpace := Proofs.M09.selectedMetricSpace g
  rw [e.carrier_eq, ← compl_eq_univ_sdiff]
  apply IsOpen.isClosed_compl
  let : PseudoEMetricSpace StandardCapSpace :=
    (Proofs.M09.selectedMetricSpace g).toPseudoEMetricSpace
  let : EDist StandardCapSpace := (Proofs.M09.selectedMetricSpace g).toEDist
  change IsOpen {x : StandardCapSpace | edist 0 x < ENNReal.ofReal e.radius}
  exact isOpen_lt (continuous_const.edist continuous_id) continuous_const

theorem endClosedTail_eq (e : StandardCylindricalEnd g) {L : ℝ} (hL : 0 ≤ L) :
    endClosedTail e L = e.carrier ∩ (fun x => (e.inverse x).2) ⁻¹' Ici L := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨end_coordinate_mem_carrier e (hL.trans hz.2), ?_⟩
    change L ≤ (e.inverse (e.coordinate z)).2
    rw [e.coordinate_left_inverse ⟨mem_univ _, hL.trans hz.2⟩]
    exact hz.2
  · rintro ⟨hx, hheight⟩
    exact ⟨e.inverse x, ⟨mem_univ _, hheight⟩, e.coordinate_right_inverse hx⟩

theorem endClosedTail_isClosed (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 0 ≤ L) : IsClosed (endClosedTail e L) := by
  rw [endClosedTail_eq e hL]
  exact e.inverse_smooth.continuousOn.snd.preimage_isClosed_of_isClosed
    (end_carrier_isClosed e) isClosed_Ici

theorem endTruncation_isOpen (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 0 ≤ L) : IsOpen (endTruncation e L) :=
  (endClosedTail_isClosed e hL).isOpen_compl

theorem endTruncation_mono (e : StandardCylindricalEnd g)
    {L R : ℝ} (hLR : L ≤ R) : endTruncation e L ⊆ endTruncation e R := by
  apply compl_subset_compl.mpr
  exact image_mono (prod_mono_right (Ici_subset_Ici.mpr hLR))

theorem endTruncation_coordinate_iff (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 0 ≤ L) {z : StandardCylinderSpace} (hz : 0 ≤ z.2) :
    e.coordinate z ∈ endTruncation e L ↔ z.2 < L := by
  change e.coordinate z ∉ endClosedTail e L ↔ _
  rw [endClosedTail_eq e hL]
  simp only [mem_inter_iff, end_coordinate_mem_carrier e hz, true_and,
    mem_preimage, mem_Ici, e.coordinate_left_inverse ⟨mem_univ _, hz⟩, not_le]

theorem endTruncatedCore_coordinate_iff (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 0 ≤ L) {z : StandardCylinderSpace} (hz : 0 ≤ z.2) :
    e.coordinate z ∈ endTruncatedCore e L ↔ z.2 ≤ L := by
  constructor
  · intro hx
    by_contra h
    exact hx ⟨z, ⟨mem_univ _, lt_of_not_ge h⟩, rfl⟩
  · rintro hheight ⟨a, ha, heq⟩
    have haz : a = z := by
      have hi := congrArg e.inverse heq
      rwa [e.coordinate_left_inverse ⟨mem_univ _, hL.trans ha.2.le⟩,
        e.coordinate_left_inverse ⟨mem_univ _, hz⟩] at hi
    rw [haz] at ha
    exact (not_lt_of_ge hheight) ha.2

theorem endTruncatedCore_isCompact (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 0 ≤ L) : IsCompact (endTruncatedCore e L) := by
  have hclosed : IsClosed (endTruncatedCore e L) :=
    (end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioi)
      (fun z hz => hL.trans_lt hz.2)).isClosed_compl
  have hstrip : IsCompact (e.coordinate '' (univ ×ˢ Icc (0 : ℝ) L)) := by
    apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    apply e.coordinate_smooth.continuousOn.mono
    intro z hz
    exact ⟨mem_univ _, by
      change -e.collar < z.2
      linarith [hz.2.1, e.collar_pos]⟩
  apply (e.core_compact.union hstrip).of_isClosed_subset hclosed
  intro x hx
  by_cases hcore : x ∈ e.closed_core
  · exact Or.inl hcore
  have hcarrier : x ∈ e.carrier := by
    rw [e.carrier_eq]
    refine ⟨mem_univ _, fun hb => hcore ?_⟩
    rw [e.closed_core_eq]
    exact (show g.edist 0 x < ENNReal.ofReal e.radius from hb).le
  have hheight : (e.inverse x).2 ≤ L := by
    by_contra h
    exact hx ⟨e.inverse x, ⟨mem_univ _, lt_of_not_ge h⟩, e.coordinate_right_inverse hcarrier⟩
  exact Or.inr ⟨e.inverse x,
    ⟨mem_univ _, e.inverse_domain x hcarrier, hheight⟩, e.coordinate_right_inverse hcarrier⟩

theorem endTruncatedCore_subset_truncation (e : StandardCylindricalEnd g)
    {L R : ℝ} (hLR : L < R) : endTruncatedCore e L ⊆ endTruncation e R := by
  intro x hx htail
  obtain ⟨z, hz, rfl⟩ := htail
  exact hx ⟨z, ⟨mem_univ _, hLR.trans_le hz.2⟩, rfl⟩

theorem endTruncation_contains_compact (e : StandardCylindricalEnd g)
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∃ L : ℝ, 1 < L ∧ K ⊆ endTruncation e L := by
  have hKC := hK.inter_right (end_carrier_isClosed e)
  have hc : ContinuousOn (fun x => (e.inverse x).2) (K ∩ e.carrier) :=
    e.inverse_smooth.continuousOn.snd.mono inter_subset_right
  obtain ⟨C, hC⟩ := (hKC.image_of_continuousOn hc).bddAbove
  let L := max 1 C + 1
  have hL : 1 < L := by dsimp [L]; linarith [le_max_left (1 : ℝ) C]
  refine ⟨L, hL, ?_⟩
  intro x hx htail
  rw [endClosedTail_eq e (by linarith)] at htail
  have hb := hC (mem_image_of_mem (fun y : StandardCapSpace => (e.inverse y).2) ⟨hx, htail.1⟩)
  have hh : L ≤ (e.inverse x).2 := htail.2
  dsimp [L] at hh
  linarith [le_max_right (1 : ℝ) C]

end PoincareConjecture.M34
