import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_PointJetConvergence









set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]



def FinitePointJetBounded (m : ℕ) (f : ι → E → F) (x : ι → E) (l : Filter ι) : Prop :=
  ∀ j ≤ m, l.IsBoundedUnder (· ≤ ·) (fun i => ‖iteratedFDeriv ℝ j (f i) (x i)‖)

namespace FinitePointJetBounded

variable {m n : ℕ} {f : ι → E → F} {x : ι → E} {l : Filter ι}



theorem mono_order (h : FinitePointJetBounded n f x l) (hmn : m ≤ n) :
    FinitePointJetBounded m f x l := fun j hj => h j (hj.trans hmn)



theorem bound_all (h : FinitePointJetBounded m f x l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in l, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (f i) (x i)‖ ≤ C := by
  classical
  choose c hc using fun j : Fin (m + 1) => (h j (by omega)).eventually_le
  let C : ℝ := ∑ j : Fin (m + 1), max (c j) 0
  refine ⟨C, Finset.sum_nonneg (fun j _ => le_max_right _ _), ?_⟩
  filter_upwards [eventually_all.mpr hc] with i hi j hj
  let k : Fin (m + 1) := ⟨j, by omega⟩
  exact (hi k).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun q _ => le_max_right (c q) 0) (Finset.mem_univ k)))



theorem zero (h : l.IsBoundedUnder (· ≤ ·) (fun i => ‖f i (x i)‖)) :
    FinitePointJetBounded 0 f x l := by
  intro j hj
  have : j = 0 := by omega
  subst j
  simpa only [norm_iteratedFDeriv_zero] using h



theorem succ_of_fderiv
    (hzero : l.IsBoundedUnder (· ≤ ·) (fun i => ‖f i (x i)‖))
    (hderiv : FinitePointJetBounded m (fun i => fderiv ℝ (f i)) x l) :
    FinitePointJetBounded (m + 1) f x l := by
  intro j hj
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hzero
  | succ j => simpa only [norm_iteratedFDeriv_fderiv] using hderiv j (by omega)



theorem fderiv (h : FinitePointJetBounded (m + 1) f x l) :
    FinitePointJetBounded m (fun i => _root_.fderiv ℝ (f i)) x l := by
  intro j hj
  simpa only [norm_iteratedFDeriv_fderiv] using h (j + 1) (by omega)



theorem congr {g : ι → E → F} (h : FinitePointJetBounded m f x l)
    (heq : ∀ i, f i =ᶠ[𝓝 (x i)] g i) : FinitePointJetBounded m g x l := by
  intro j hj
  have hh : (fun i => ‖iteratedFDeriv ℝ j (f i) (x i)‖) =
      fun i => ‖iteratedFDeriv ℝ j (g i) (x i)‖ := by
    funext i
    rw [((heq i).iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
  rw [← hh]
  exact h j hj



theorem prodMk {g : ι → E → G}
    (hf : FinitePointJetBounded m f x l) (hg : FinitePointJetBounded m g x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) :
    FinitePointJetBounded m (fun i y => (f i y, g i y)) x l := by
  intro j hj
  obtain ⟨A, hA⟩ := (hf j hj).eventually_le
  obtain ⟨B, hB⟩ := (hg j hj).eventually_le
  refine ⟨max A B, ?_⟩
  change ∀ᶠ i in l, ‖iteratedFDeriv ℝ j (fun y => (f i y, g i y)) (x i)‖ ≤ max A B
  filter_upwards [hA, hB] with i hiA hiB
  rw [iteratedFDeriv_prodMk (hfs i) (hgs i) (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max hiA hiB




theorem comp {g : ι → F → G}
    (hf : FinitePointJetBounded m f x l)
    (hg : FinitePointJetBounded m g (fun i => f i (x i)) l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (f i (x i))) :
    FinitePointJetBounded m (fun i => g i ∘ f i) x l := by
  obtain ⟨A, _, hA⟩ := hf.bound_all
  obtain ⟨B, _, hB⟩ := hg.bound_all
  intro j hj
  refine ⟨j.factorial * B * (max A 1) ^ j, ?_⟩
  change ∀ᶠ i in l, ‖iteratedFDeriv ℝ j (g i ∘ f i) (x i)‖ ≤
    j.factorial * B * (max A 1) ^ j
  filter_upwards [hA, hB] with i hiA hiB
  apply Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_le_of_contDiffAt
    (hfs i) (hgs i) j
  · intro k hk
    exact hiB k (hk.trans hj)
  · intro k hk hk'
    exact (hiA k (hk'.trans hj)).trans
      ((le_max_left A 1).trans (le_self_pow₀ (le_max_right A 1) (by omega)))




theorem smooth_postcompose [FiniteDimensional ℝ F] {g : F → G}
    (hf : FinitePointJetBounded m f x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i)) (hg : ContDiff ℝ ∞ g) :
    FinitePointJetBounded m (fun i => g ∘ f i) x l := by
  let : ProperSpace F := FiniteDimensional.proper ℝ F
  obtain ⟨A, hA⟩ := (hf 0 (Nat.zero_le _)).eventually_le
  have hout : FinitePointJetBounded m (fun _ : ι => g) (fun i => f i (x i)) l := by
    intro j _
    have hc : ContinuousOn (iteratedFDeriv ℝ j g) (Metric.closedBall (0 : F) A) :=
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : F) A).exists_bound_of_continuousOn hc
    refine ⟨B, ?_⟩
    change ∀ᶠ i in l, ‖iteratedFDeriv ℝ j g (f i (x i))‖ ≤ B
    filter_upwards [hA] with i hi
    apply hB
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_iteratedFDeriv_zero] using hi
  exact hf.comp hout hfs (fun _ => hg.contDiffAt)

end FinitePointJetBounded



theorem PointJetsConverge.finite_bound {f : ι → E → F} {x : ι → E}
    {f0 : E → F} {x0 : E} {l : Filter ι}
    (h : PointJetsConverge f x f0 x0 l) (m : ℕ) : FinitePointJetBounded m f x l :=
  fun j _ => h.bounded j

end PoincareConjecture.M45
