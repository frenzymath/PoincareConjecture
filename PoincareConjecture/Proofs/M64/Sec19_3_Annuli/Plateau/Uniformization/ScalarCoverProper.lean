import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLevelProper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

def scalarNormalizedCoverMap (H : Plane → ℝ) (V : Cover → ℝ) (P : ℝ)
    (z : Cover) : Cover := (H (scalarCoverMap z), V z / P)

theorem scalarNormalizedCoverMap_continuousOn {H : Plane → ℝ} (hHc : Continuous H)
    {V : Cover → ℝ} (hVc : ContinuousOn V scalarCoverStrip) (P : ℝ) :
    ContinuousOn (scalarNormalizedCoverMap H V P) scalarCoverStrip :=
  (hHc.comp scalarCoverMap_smooth.continuous).continuousOn.prodMk
    (hVc.div_const P)

theorem scalarCover_deck_defect_bounded {V : Cover → ℝ}
    (hVc : ContinuousOn V scalarCoverStrip) {P : ℝ}
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    {a b : ℝ} (ha : 1 < a) (hb : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Cover, z.1 ∈ Icc a b → |V z - P * z.2| ≤ C := by
  let K : Set Cover := Icc (a, 0) (b, 1)
  have hKsub : K ⊆ scalarCoverStrip :=
    fun z hz => ⟨ha.trans_le hz.1.1, hz.2.1.trans_lt hb⟩
  have hfc : ContinuousOn (fun z : Cover => V z - P * z.2) K :=
    (hVc.mono hKsub).sub (continuous_const.mul continuous_snd).continuousOn
  obtain ⟨C, hC⟩ := (show IsCompact K from isCompact_Icc).exists_bound_of_continuousOn hfc
  refine ⟨max 0 C, le_max_left _ _, fun z hz => ?_⟩
  have hp : Function.Periodic (fun t : ℝ => V (z.1, t) - P * t) 1 := by
    intro t
    have hd := hdeck (z.1, t) ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
    simp only [Prod.mk_add_mk, add_zero] at hd
    dsimp only
    rw [hd]
    ring
  have heq : V (z.1, Int.fract z.2) - P * Int.fract z.2 = V z - P * z.2 := by
    simpa only [Int.fract, mul_one, Prod.eta] using hp.sub_int_mul_eq (Int.floor z.2)
  have hmem : (z.1, Int.fract z.2) ∈ K :=
    ⟨⟨hz.1, Int.fract_nonneg _⟩, ⟨hz.2, (Int.fract_lt_one _).le⟩⟩
  have hbound := hC _ hmem
  rw [Real.norm_eq_abs, heq] at hbound
  exact hbound.trans (le_max_right _ _)

theorem scalarNormalizedCoverMap_compact_preimage {H : Plane → ℝ}
    (hHc : Continuous H)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {V : Cover → ℝ} (hVc : ContinuousOn V scalarCoverStrip) {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    {K : Set Cover} (hK : IsCompact K) (hKsub : K ⊆ {y : Cover | y.1 ∈ Ioo (0 : ℝ) 1}) :
    IsCompact (scalarCoverStrip ∩ scalarNormalizedCoverMap H V P ⁻¹' K) := by
  obtain ⟨a, b, ha, -, hb, hab⟩ := scalarPotential_levels_radially_separated
    hHc hinner houter (hK.image continuous_fst) (by
      rintro u ⟨y, hy, rfl⟩
      exact hKsub hy)
  obtain ⟨C, hC, hdefect⟩ := scalarCover_deck_defect_bounded hVc hdeck ha hb
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_snd.continuousOn
  let T : ℝ := max 0 B + C / P
  let S : Set Cover := Icc (a, -T) (b, T)
  have hSsub : S ⊆ scalarCoverStrip :=
    fun z hz => ⟨ha.trans_le hz.1.1, hz.2.1.trans_lt hb⟩
  have hbound : scalarCoverStrip ∩ scalarNormalizedCoverMap H V P ⁻¹' K ⊆ S := by
    intro z hz
    have hr : z.1 ∈ Icc a b := by
      have hn := hab (scalarCoverMap z) (scalarCoverMap_mem hz.1) ⟨_, hz.2, rfl⟩
      simpa only [scalarCoverMap, scalarCirclePoint_norm,
        abs_of_pos (zero_lt_one.trans hz.1.1)] using hn
    have hV : |V z / P| ≤ max 0 B := by
      have h := hB _ hz.2
      exact (show |V z / P| ≤ B from h).trans (le_max_right _ _)
    have ht : |z.2| ≤ T := by
      calc
        |z.2| = |V z / P - (V z - P * z.2) / P| := by
          congr 1
          field_simp
          ring
        _ ≤ |V z / P| + |(V z - P * z.2) / P| := abs_sub _ _
        _ ≤ max 0 B + C / P := by
          apply add_le_add hV
          rw [abs_div, abs_of_pos hP]
          exact div_le_div_of_nonneg_right (hdefect z hr) hP.le
    exact ⟨⟨hr.1, (abs_le.mp ht).1⟩, ⟨hr.2, (abs_le.mp ht).2⟩⟩
  have heq : scalarCoverStrip ∩ scalarNormalizedCoverMap H V P ⁻¹' K =
      S ∩ scalarNormalizedCoverMap H V P ⁻¹' K := by
    ext z
    exact ⟨fun hz => ⟨hbound hz, hz.2⟩, fun hz => ⟨hSsub hz.1, hz.2⟩⟩
  rw [heq]
  have hFc : ContinuousOn (scalarNormalizedCoverMap H V P) S :=
    (scalarNormalizedCoverMap_continuousOn hHc hVc P).mono hSsub
  have hclosed := hFc.preimage_isClosed_of_isClosed
    (show IsClosed S from isClosed_Icc) hK.isClosed
  exact (show IsCompact S from isCompact_Icc).of_isClosed_subset hclosed inter_subset_left

end PoincareConjecture.M64Uniformization
