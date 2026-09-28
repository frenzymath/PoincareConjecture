import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.PhaseContactTransfer
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.WindingInvariance



set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem real_circle_lift_difference_eqOn {u v c : ℝ} {r s : ℝ → ℝ}
    (hr : ContinuousOn r (Icc u v)) (hs : ContinuousOn s (Icc u v))
    (hproj : ∀ t ∈ Icc u v, (r t : Circle) = ((c + s t : ℝ) : Circle))
    {x : ℝ} (hx : x ∈ Icc u v) :
    ∀ t ∈ Icc u v, r t - (c + s t) = r x - (c + s x) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have hz (t : ℝ) (ht : t ∈ Icc u v) : ((r t - (c + s t) : ℝ) : Circle) = 0 := by
    rw [AddCircle.coe_sub, hproj t ht, sub_self]
  intro t ht
  exact (AddCircle.isCoveringMap_coe (4 * (8 : ℝ))).constOn_of_comp
    isPreconnected_Icc (hr.sub (continuousOn_const.add hs))
    (fun y hy z hz' => (hz y hy).trans (hz z hz').symm) ht hx

theorem exists_affine_lift_germ_of_common_window
    {D E : Set P2} {a b c : ℝ} (ha : a < 0) (hb : 0 < b)
    (hD : D ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (hE : E ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (H J : P2 ≃ₜ P2)
    (hfix : ∀ y, y ∉ interior D → H y = y)
    (jfix : ∀ y, y ∉ interior E → J y = y)
    (G : Ann ≃ₜ Ann)
    (hwindow : ∀ (z : Ann) (y : P2), y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      (z : P2) = annularLiftProjectionAt c y →
      (G z : P2) = annularLiftProjectionAt c (J (H y)))
    (gamma : C(I, Ann)) (r r' : ℝ → P2)
    (hr : ContinuousOn r (Icc 0 1)) (hr' : ContinuousOn r' (Icc 0 1))
    (hheight : ∀ t : I, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hheight' : ∀ t : I, (r' t).2 ∈ Icc (-1 : ℝ) 1)
    (hproject : ∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = gamma t)
    (hproject' : ∀ t : I, annulusMap 8 (by norm_num) (((r' t).1 : Circle), (r' t).2) = G (gamma t))
    (k : ℤ) {x u v m d : ℝ}
    (hu : 0 ≤ u) (hux : u < x) (hxv : x < v) (hv : v ≤ 1) (hm : m ≠ 0)
    (hzero : (J (H ((r x).2, (r x).1 - (c + 32 * (k : ℝ))))).2 = 0)
    (hgerm : ∀ y ∈ Icc u v,
      (J (H ((r y).2, (r y).1 - (c + 32 * (k : ℝ))))).2 = m * (y - x))
    (hx' : (r' x).1 = d) :
    ∃ u' v' m' : ℝ, 0 ≤ u' ∧ u' < x ∧ x < v' ∧ v' ≤ 1 ∧ m' ≠ 0 ∧
      ∀ y ∈ Icc u' v', (r' y).1 - d = m' * (y - x) := by
  let Q (t : ℝ) : P2 := ((r t).2, (r t).1 - (c + 32 * (k : ℝ)))
  let P (t : ℝ) : P2 := J (H (Q t))
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hu hux, lt_of_lt_of_le hxv hv⟩
  have hrc : ContinuousAt r x := (hr x (Ioo_subset_Icc_self hx01)).continuousAt
    (Icc_mem_nhds hx01.1 hx01.2)
  have hpc : ContinuousAt (fun t => (P t).2) x := by dsimp [P, Q]; fun_prop
  have hnear : {t | (P t).2 ∈ Ioo a b} ∩ Ioo u v ∈ 𝓝 x :=
    Filter.inter_mem (hpc.preimage_mem_nhds (Ioo_mem_nhds (by simpa [P, Q, hzero] using ha)
      (by simpa [P, Q, hzero] using hb))) (Ioo_mem_nhds hux hxv)
  obtain ⟨l, w, hxw, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let u' := (l + x) / 2
  let v' := (x + w) / 2
  have hsmall : Icc u' v' ⊆ {t | (P t).2 ∈ Ioo a b} ∩ Ioo u v := by
    intro t ht
    apply hsub
    constructor <;> dsimp [u', v'] at ht ⊢ <;> linarith [hxw.1, hxw.2, ht.1, ht.2]
  have hu'x : u' < x := by dsimp [u']; linarith [hxw.1]
  have hxv' : x < v' := by dsimp [v']; linarith [hxw.2]
  have hinterval : Icc u' v' ⊆ Icc u v := fun t ht => Ioo_subset_Icc_self (hsmall ht).2
  have h01 : Icc u' v' ⊆ Icc (0 : ℝ) 1 :=
    hinterval.trans (Icc_subset_Icc hu hv)
  have hheightP (t : ℝ) (ht : t ∈ Icc u' v') : (P t).1 ∈ Icc (-1 : ℝ) 1 :=
    (supported_homeomorph_mem_iff (fun z hz => (hE hz).1) J jfix (H (Q t))).mp
      ((supported_homeomorph_mem_iff (fun z hz => (hD hz).1) H hfix (Q t)).mp
        (hheight ⟨t, h01 ht⟩))
  have hphase (t : ℝ) (ht : t ∈ Icc u' v') :
      ((r' t).1 : Circle) = ((c + (P t).2 : ℝ) : Circle) := by
    have hPt : P t ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
      ⟨hheightP t ht, Ioo_subset_Icc_self (hsmall ht).1⟩
    have hQt := (supported_homeomorph_mem_iff hD H hfix (Q t)).mpr
      ((supported_homeomorph_mem_iff hE J jfix (H (Q t))).mpr hPt)
    have hq : (gamma ⟨t, h01 ht⟩ : P2) = annularLiftProjectionAt c (Q t) := by
      rw [← hproject]
      have hp : ((32 * (k : ℝ) : ℝ) : Circle) = 0 :=
        (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨k, by simp [zsmul_eq_mul]; ring⟩
      change annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) =
        annulusMap 8 (by norm_num) (((c + ((r t).1 - (c + 32 * (k : ℝ))) : ℝ) : Circle), (r t).2)
      rw [show c + ((r t).1 - (c + 32 * (k : ℝ))) = (r t).1 - 32 * (k : ℝ) by ring,
        AddCircle.coe_sub, hp, sub_zero]
    have heq := (hproject' ⟨t, h01 ht⟩).trans (hwindow (gamma ⟨t, h01 ht⟩) (Q t) hQt hq)
    exact congrArg Prod.fst (injective_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)
      (a₁ := (((r' t).1 : Circle), ⟨(r' t).2, hheight' ⟨t, h01 ht⟩⟩))
      (a₂ := (((c + (P t).2 : ℝ) : Circle), ⟨(P t).1, hheightP t ht⟩)) heq)
  have hPc : ContinuousOn (fun t => (P t).2) (Icc u' v') := by
    exact continuous_snd.comp_continuousOn (J.continuous.comp_continuousOn
      (H.continuous.comp_continuousOn ((hr.mono h01).snd.prodMk
        ((hr.mono h01).fst.sub continuousOn_const))))
  have hdiff := real_circle_lift_difference_eqOn ((hr'.mono h01).fst) hPc hphase
    (show x ∈ Icc u' v' from ⟨hu'x.le, hxv'.le⟩)
  refine ⟨u', v', m, (h01 ⟨le_rfl, hu'x.le.trans hxv'.le⟩).1, hu'x, hxv',
    (h01 ⟨hu'x.le.trans hxv'.le, le_rfl⟩).2, hm, ?_⟩
  intro y hy
  have hd := hdiff y hy
  have hg := hgerm y (hinterval hy)
  change (P y).2 = m * (y - x) at hg
  change (r' y).1 - (c + (P y).2) = (r' x).1 - (c + (P x).2) at hd
  have hp0 : (P x).2 = 0 := hzero
  rw [hx', hp0] at hd
  linarith

end PoincareConjecture.M76.Dehn
