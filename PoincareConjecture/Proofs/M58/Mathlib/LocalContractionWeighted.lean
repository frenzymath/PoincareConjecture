import PoincareConjecture.Proofs.M58.Mathlib.LocalContractionChart
import Mathlib.Topology.Algebra.Support










set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M58

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]




noncomputable def weightedChartContraction (c : M) (b : M → ℝ)
    (v : ℝ × (M × M)) : M := by
  classical
  exact if v.2.1 ∈ (extChartAt I c).source ∧ v.2.2 ∈ (extChartAt I c).source then
    chartContraction I c (v.1 * b v.2.1, v.2.1, v.2.2) else v.2.2



theorem weightedChartContraction_of_weight_zero (c : M) (b : M → ℝ)
    (t : ℝ) (p q : M) (hb : b p = 0) :
    weightedChartContraction I c b (t, p, q) = q := by
  classical
  unfold weightedChartContraction
  split_ifs with h
  · simpa only [hb, mul_zero] using chartContraction_zero I c p q h.2
  · rfl



theorem weightedChartContraction_zero (c : M) (b : M → ℝ) (p q : M) :
    weightedChartContraction I c b (0, p, q) = q := by
  classical
  unfold weightedChartContraction
  split_ifs with h
  · simpa only [zero_mul] using chartContraction_zero I c p q h.2
  · rfl



theorem weightedChartContraction_diagonal (c : M) (b : M → ℝ) (t : ℝ) (p : M) :
    weightedChartContraction I c b (t, p, p) = p := by
  classical
  unfold weightedChartContraction
  split_ifs with h
  · exact chartContraction_diagonal I c p h.1 _
  · rfl



theorem weightedChartContraction_one (c : M) (b : M → ℝ) (p q : M)
    (hp : p ∈ (extChartAt I c).source) (hq : q ∈ (extChartAt I c).source)
    (hb : b p = 1) : weightedChartContraction I c b (1, p, q) = p := by
  classical
  simp only [weightedChartContraction, hp, hq, and_self, ↓reduceIte, hb, one_mul]
  exact chartContraction_one I c p q hp

variable [I.Boundaryless] [IsManifold I ∞ M]




theorem contMDiffAt_weightedChartContraction_diagonal (c : M) (b : M → ℝ)
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hsupp : tsupport b ⊆ (extChartAt I c).source) (t : ℝ) (p : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞
      (weightedChartContraction I c b) (t, p, p) := by
  classical
  by_cases hp : p ∈ tsupport b
  · have hsource := hsupp hp
    have hinput : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I))
        (𝓘(ℝ, ℝ).prod (I.prod I)) ∞
        (fun w : ℝ × (M × M) => (w.1 * b w.2.1, w.2)) (t, p, p) :=
      (contMDiffAt_fst.smul (hb.contMDiffAt.comp _
        (contMDiffAt_fst.comp _ contMDiffAt_snd))).prodMk contMDiffAt_snd
    have hmain := (contMDiffAt_chartContraction_diagonal I c p hsource (t * b p)).comp
      (t, p, p) hinput
    apply hmain.congr_of_eventuallyEq
    have hleft : ∀ᶠ w : ℝ × (M × M) in 𝓝 (t, p, p),
        w.2.1 ∈ (extChartAt I c).source :=
      (continuous_snd.fst.tendsto (t, p, p))
        ((isOpen_extChartAt_source c).mem_nhds hsource)
    have hright : ∀ᶠ w : ℝ × (M × M) in 𝓝 (t, p, p),
        w.2.2 ∈ (extChartAt I c).source :=
      (continuous_snd.snd.tendsto (t, p, p))
        ((isOpen_extChartAt_source c).mem_nhds hsource)
    filter_upwards [hleft, hright] with w hwp hwq
    simp only [weightedChartContraction, hwp, hwq, and_self, ↓reduceIte, Function.comp_apply]
  · have hproj : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞
        (fun w : ℝ × (M × M) => w.2.2) (t, p, p) :=
      contMDiffAt_snd.comp _ contMDiffAt_snd
    apply hproj.congr_of_eventuallyEq
    have hzero : ∀ᶠ w : ℝ × (M × M) in 𝓝 (t, p, p), w.2.1 ∉ tsupport b :=
      (continuous_snd.fst.tendsto (t, p, p)) ((isClosed_tsupport b).isOpen_compl.mem_nhds hp)
    filter_upwards [hzero] with w hw
    apply weightedChartContraction_of_weight_zero
    by_contra hne
    exact hw (subset_closure hne)

end PoincareConjecture.Proofs.M58
