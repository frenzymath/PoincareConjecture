import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.SliceContact
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.ValueContinuity
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.InitialSliceValue
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.CappedMinimumComparison










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}



theorem cappedSliceAction_contact
    (hCoordinates : M12MetricPredecessors.{0} 3)
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {b c : ℝ} (hb : 0 < b) (hbc : b < c) (hc : c ^ 2 ≤ T - start) :
    ∃ phi : ℝ → ℝ, ∃ d : ℝ, HasDerivAt phi d b ∧
      phi b = cappedSliceAction G T x C.barrier b / (2 * b) ∧
      (∀ᶠ s in 𝓝[>] b, cappedSliceAction G T x C.barrier s / (2 * s) ≤ phi s) ∧
      d ≤ max ((3 - 2 * (cappedSliceAction G T x C.barrier b / (2 * b))) / b)
        (-(cappedSliceAction G T x C.barrier b / (2 * b)) / b) := by
  by_cases hactive : cappedSliceAction G T x C.barrier b < C.barrier
  · obtain ⟨phi, d, hphi, heq, hnear, hd⟩ :=
      cappedSliceAction_active_contact hCoordinates hM04 hM12 LG E C hstrip hb hbc hc hactive
    exact ⟨phi, d, hphi, heq, hnear, hd.trans (le_max_left _ _)⟩
  have hcpos := hb.trans hbc
  have hbStart := ((sq_le_sq₀ hb.le hcpos.le).mpr hbc.le).trans hc
  have heq : cappedSliceAction G T x C.barrier b = C.barrier :=
    le_antisymm (cappedSliceAction_alternative hM04 hM12 LG E C hb hbStart).1
      (le_of_not_gt hactive)
  have hder : HasDerivAt (fun s : ℝ => C.barrier / (2 * s))
      (-(C.barrier / (2 * b)) / b) b := by
    convert (hasDerivAt_const b C.barrier).div ((hasDerivAt_id b).const_mul 2)
      (by positivity : 2 * b ≠ 0) using 1 <;> try rfl
    dsimp only [id_eq]
    field_simp [hb.ne']
    ring
  refine ⟨fun s => C.barrier / (2 * s), -(C.barrier / (2 * b)) / b,
    hder, by dsimp; rw [heq], ?_, ?_⟩
  · have hnear : ∀ᶠ s in 𝓝[>] b, s ∈ Ioo 0 c :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hb hbc)
    filter_upwards [hnear] with s hs
    have hsStart := ((sq_le_sq₀ hs.1.le hcpos.le).mpr hs.2.le).trans hc
    exact div_le_div_of_nonneg_right
      (cappedSliceAction_alternative hM04 hM12 LG E C hs.1 hsStart).1
      (mul_nonneg (by norm_num) hs.1.le)
  · rw [heq]
    exact le_max_right _ _




theorem cappedSliceAction_le_three_mul
    (hCoordinates : M12MetricPredecessors.{0} 3)
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {b : ℝ} (hb : 0 < b) (hbStart : b ^ 2 ≤ T - start) :
    cappedSliceAction G T x C.barrier b ≤ 3 * b := by
  obtain ⟨a, ha, hab, hstart⟩ :=
    exists_initial_cappedSliceAction_bound hM04 hM12 LG E C hstrip hb hbStart
  let f (s : ℝ) := cappedSliceAction G T x C.barrier s / (2 * s)
  have hf : ContinuousOn f (Icc a b) :=
    (cappedSliceAction_continuousOn hM04 hM12 LG E C hstrip ha hbStart).div
      (continuous_const.mul continuous_id).continuousOn
      (fun s hs => ne_of_gt (mul_pos (by norm_num) (ha.trans_le hs.1)))
  have hcontact : ∀ t ∈ Ico a b, ∃ phi : ℝ → ℝ, ∃ d : ℝ,
      HasDerivAt phi d t ∧ phi t = f t ∧
      (∀ᶠ s in 𝓝[>] t, f s ≤ phi s) ∧
      d ≤ max ((3 - 2 * f t) / t) (-f t / t) := by
    intro t ht
    exact cappedSliceAction_contact hCoordinates hM04 hM12 LG E C hstrip
      (ha.trans_le ht.1) ht.2 hbStart
  have hbound := capped_minimum_le_of_upper_competitors ha hf hstart hcontact b ⟨hab, le_rfl⟩
  have hmul := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hb)).mp hbound
  nlinarith

end PoincareConjecture.Proofs.M46
