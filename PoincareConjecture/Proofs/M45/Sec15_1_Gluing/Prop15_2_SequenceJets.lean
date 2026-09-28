import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_EvolvingJets
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_VanishingOperations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

variable {ι : Type*} {l : Filter ι}

theorem eventually_le_floor_inv {eta : ι → ℝ}
    (hpos : ∀ i, 0 < eta i) (hzero : Tendsto eta l (𝓝 0)) (m : ℕ) :
    ∀ᶠ i in l, m ≤ ⌊(eta i)⁻¹⌋₊ := by
  have hd : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  filter_upwards [hzero.eventually (gt_mem_nhds hd)] with i hi
  apply Nat.le_floor
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (hpos i)).mpr
  have hb := (lt_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mp hi
  nlinarith only [hb, hpos i]

theorem evolvingCylinderError_pointJetsVanish
    {eta t : ι → ℝ} {B : ι → RoundCylinderTwoTensor} {z : ι → RoundCylinderSpace}
    (hpos : ∀ i, 0 < eta i) (hzero : Tendsto eta l (𝓝 0))
    (ht : ∀ i, t i ∈ Icc (-1 : ℝ) 0)
    (hB : ∀ i, RoundCylinderClose (eta i) (t i) (B i))
    (hz : ∀ i, (z i).2 ∈ Ioo (-(eta i)⁻¹) (eta i)⁻¹) :
    PointJetsVanish (fun i p => M36.centeredCylinderMetric (B i) (z i).1 (z i).2 p -
      M44.evolvingCylinderModelField (t i) p) (fun _ => 0) l := by
  intro m
  obtain ⟨C, hC, hbound⟩ := exists_evolvingCylinderError_jet_bound m
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [eventually_le_floor_inv hpos hzero m] with i hi
    exact hbound (hpos i) (ht i) (hB i) hi (z i) (hz i)
  · simpa only [mul_zero] using hzero.const_mul C

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem PointJetsConverge.of_sub_vanish {f g : ι → E → F} {x : ι → E}
    {f0 : E → F} {x0 : E}
    (hg : PointJetsConverge g x f0 x0 l)
    (he : PointJetsVanish (fun i y => f i y - g i y) x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) : PointJetsConverge f x f0 x0 l := by
  intro m
  have h := (he m).add (hg m)
  simpa only [fun_iteratedFDeriv_sub_apply
    ((hfs _).of_le (by exact_mod_cast le_top))
    ((hgs _).of_le (by exact_mod_cast le_top)), sub_add_cancel, zero_add] using h

theorem PointJetsConverge.const_smul_family {f : ι → E → F} {x : ι → E}
    {f0 : E → F} {x0 : E} {c : ι → ℝ} {c0 : ℝ}
    (hf : PointJetsConverge f x f0 x0 l) (hc : Tendsto c l (𝓝 c0))
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i)) (hf0 : ContDiffAt ℝ ∞ f0 x0) :
    PointJetsConverge (fun i y => c i • f i y) x (fun y => c0 • f0 y) x0 l := by
  intro m
  simpa only [iteratedFDeriv_const_smul_apply'
    ((hfs _).of_le (by exact_mod_cast le_top)), iteratedFDeriv_const_smul_apply'
      (hf0.of_le (by exact_mod_cast le_top))] using hc.smul (hf m)

end PoincareConjecture.M45
