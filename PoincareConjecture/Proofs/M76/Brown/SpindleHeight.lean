import PoincareConjecture.Proofs.M76.Brown.SpindleCoordinates
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.ContinuousMap.Basic










set_option autoImplicit false

open Set Metric

namespace BrownCollar

variable {B : Type*} [MetricSpace B]


def collarBase (b : B) : B × Ico (0 : ℝ) 1 := (b, ⟨0, by constructor <;> norm_num⟩)





theorem exists_spindleHeight {U : Set B} (hU : IsOpen U)
    {O : Set (B × Ico (0 : ℝ) 1)} (hO : IsOpen O)
    (hUO : ∀ b ∈ closure U, collarBase b ∈ O) :
    ∃ height : C(B, ℝ), (∀ b, height b ∈ Icc (0 : ℝ) 1) ∧
      (∀ b, 0 < height b ↔ b ∈ U) ∧
      closure {z : B × Ico (0 : ℝ) 1 | (z.2 : ℝ) < height z.1} ⊆ O := by
  classical
  have hsupp : ∃ a : C(B, ℝ), (∀ b, a b ∈ Icc (0 : ℝ) 1) ∧
      ∀ b, 0 < a b ↔ b ∈ U := by
    by_cases hUc : Uᶜ.Nonempty
    · refine ⟨⟨fun b => min 1 (infDist b Uᶜ),
        continuous_const.min (continuous_infDist_pt Uᶜ)⟩, ?_, ?_⟩
      · intro b
        exact ⟨le_min zero_le_one infDist_nonneg, min_le_left _ _⟩
      · intro b
        change 0 < min 1 (infDist b Uᶜ) ↔ b ∈ U
        rw [lt_min_iff, and_iff_right zero_lt_one]
        simpa only [notMem_compl_iff] using
          (hU.isClosed_compl.notMem_iff_infDist_pos hUc).symm
    · have hUall : U = univ := eq_univ_of_forall fun b => by
        by_contra hb
        exact hUc ⟨b, hb⟩
      refine ⟨⟨fun _ => 1, continuous_const⟩, ?_, ?_⟩
      · intro b
        exact ⟨zero_le_one, le_rfl⟩
      · intro b
        simp only [ContinuousMap.coe_mk, hUall, mem_univ, zero_lt_one]
  obtain ⟨a, ha, hapos⟩ := hsupp
  let F : Set (B × Ico (0 : ℝ) 1) := Oᶜ ∪ {z | (1 / 2 : ℝ) ≤ (z.2 : ℝ)}
  have hheight : Continuous (fun z : B × Ico (0 : ℝ) 1 => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hF : IsClosed F := hO.isClosed_compl.union (isClosed_le continuous_const hheight)
  have hFne (b : B) : F.Nonempty := by
    refine ⟨(b, ⟨1 / 2, by constructor <;> norm_num⟩), Or.inr ?_⟩
    change (1 / 2 : ℝ) ≤ 1 / 2
    exact le_rfl
  let d : B → ℝ := fun b => infDist (collarBase b) F
  have hd : Continuous d := (continuous_infDist_pt F).comp
    (continuous_id.prodMk continuous_const)
  have hdpos (b : B) (hb : b ∈ closure U) : 0 < d b := by
    apply (hF.notMem_iff_infDist_pos (hFne b)).mp
    rintro (hbO | hbheight)
    · exact hbO (hUO b hb)
    · change (1 / 2 : ℝ) ≤ 0 at hbheight
      norm_num at hbheight
  let height : C(B, ℝ) := ⟨fun b => min (a b) (d b) / 2, (a.continuous.min hd).div_const 2⟩
  have hlea (b : B) : height b ≤ a b / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hled (b : B) : height b ≤ d b / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hbounds (b : B) : height b ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (le_min (ha b).1 infDist_nonneg) (by norm_num)
    · have hb := (ha b).2
      have hb' := hlea b
      linarith
  have hpos (b : B) : 0 < height b ↔ b ∈ U := by
    constructor
    · intro hb
      apply (hapos b).mp
      have hb' := hlea b
      linarith
    · intro hb
      exact div_pos (lt_min ((hapos b).mpr hb) (hdpos b (subset_closure hb))) (by norm_num)
  refine ⟨height, hbounds, hpos, ?_⟩
  let A := {z : B × Ico (0 : ℝ) 1 | (z.2 : ℝ) < height z.1}
  have hproj : closure A ⊆ (Prod.fst : B × Ico (0 : ℝ) 1 → B) ⁻¹' closure U := by
    apply closure_minimal _ (isClosed_closure.preimage continuous_fst)
    intro z hz
    exact subset_closure ((hpos z.1).mp (z.2.property.1.trans_lt hz))
  have hupper : closure A ⊆ {z : B × Ico (0 : ℝ) 1 | (z.2 : ℝ) ≤ height z.1} :=
    closure_minimal (by
      intro z hz
      change (z.2 : ℝ) ≤ height z.1
      exact hz.le)
      (isClosed_le hheight (height.continuous.comp continuous_fst))
  intro z hz
  have hdpositive := hdpos z.1 (hproj hz)
  have hlt : (z.2 : ℝ) < d z.1 := (hupper hz).trans_lt
    ((hled z.1).trans_lt (by linarith))
  have hdist : dist (collarBase z.1) z = (z.2 : ℝ) := by
    rcases z with ⟨b, t⟩
    simp only [collarBase, dist_prod_same_left, Subtype.dist_eq, Real.dist_eq,
      zero_sub, abs_neg, abs_of_nonneg t.property.1]
  have hsmall : dist (collarBase z.1) z < infDist (collarBase z.1) F := by
    rw [hdist]
    exact hlt
  have hnF : z ∉ F := notMem_of_dist_lt_infDist hsmall
  by_contra hzO
  exact hnF (Or.inl hzO)

end BrownCollar
