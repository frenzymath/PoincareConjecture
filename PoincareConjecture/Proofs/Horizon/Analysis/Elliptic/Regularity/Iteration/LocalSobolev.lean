import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.WeakDerivatives
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.Multiply
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.LocalL2

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Euclidean

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def MemWkpLocally (k : ℕ) (u : E → ℝ) (O : Set E) : Prop :=
  ∀ x ∈ O, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ MemWkp k 2 u V

theorem locally_of_memWkp {O : Set E} (hO : IsOpen O) {k : ℕ} {u : E → ℝ}
    (hu : MemWkp k 2 u O) : MemWkpLocally k u O :=
  fun _ hx => ⟨O, hO, hx, Subset.rfl, hu⟩

theorem MemWkpLocally.restrict {O V : Set E} {k : ℕ} {u : E → ℝ}
    (hu : MemWkpLocally k u O) (hV : IsOpen V) (hVO : V ⊆ O) :
    MemWkpLocally k u V := by
  intro x hx
  obtain ⟨W, hW, hxW, hWO, huW⟩ := hu x (hVO hx)
  exact ⟨W ∩ V, hW.inter hV, ⟨hxW, hx⟩, inter_subset_right,
    huW.mono_set (by norm_num) (hW.inter hV) inter_subset_left⟩

theorem MemWkpLocally.mono_order {O : Set E} {k l : ℕ} {u : E → ℝ}
    (hu : MemWkpLocally l u O) (hkl : k ≤ l) : MemWkpLocally k u O := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, huV⟩ := hu x hx
  exact ⟨V, hV, hxV, hVO, huV.le_of_le hkl⟩

theorem MemWkpLocally.zero {O : Set E} (hO : IsOpen O) (k : ℕ) :
    MemWkpLocally k (fun _ : E => 0) O :=
  locally_of_memWkp hO (MemWkp_zero_fun (by norm_num) hO)

theorem MemWkpLocally.add {O : Set E} {k : ℕ} {u v : E → ℝ}
    (hu : MemWkpLocally k u O) (hv : MemWkpLocally k v O) :
    MemWkpLocally k (fun x => u x + v x) O := by
  intro x hx
  obtain ⟨U, hU, hxU, hUO, huU⟩ := hu x hx
  obtain ⟨V, hV, hxV, _, hvV⟩ := hv x hx
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, inter_subset_left.trans hUO, ?_⟩
  exact MemWkp.add (by norm_num) (hU.inter hV)
    (huU.mono_set (by norm_num) (hU.inter hV) inter_subset_left)
    (hvV.mono_set (by norm_num) (hU.inter hV) inter_subset_right)

theorem MemWkpLocally.sum {ι : Type*} {O : Set E} (hO : IsOpen O)
    {k : ℕ} (s : Finset ι) {u : ι → E → ℝ}
    (hu : ∀ i ∈ s, MemWkpLocally k (u i) O) :
    MemWkpLocally k (fun x => ∑ i ∈ s, u i x) O := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MemWkpLocally.zero hO k
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hu i (Finset.mem_insert_self i s)).add
          (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem MemWkpLocally.exists_common_neighborhood {ι : Type*} [Fintype ι]
    {O : Set E} (hO : IsOpen O) {k : ℕ} {u : ι → E → ℝ}
    (hu : ∀ i, MemWkpLocally k (u i) O) {x : E} (hx : x ∈ O) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ ∀ i, MemWkp k 2 (u i) V := by
  classical
  choose V hV hxV hVO huV using fun i => hu i x hx
  let W := O ∩ ⋂ i, V i
  have hW : IsOpen W := hO.inter (isOpen_iInter_of_finite hV)
  refine ⟨W, hW, ⟨hx, mem_iInter.mpr hxV⟩, inter_subset_left, fun i => ?_⟩
  exact (huV i).mono_set (by norm_num) hW
    (fun y hy => mem_iInter.mp hy.2 i)

private theorem exists_iteratedFDeriv_bound_on_compact {a : E → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) {K : Set E} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, ∀ j ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ j a x‖ ≤ C := by
  classical
  have hbound (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j a x‖ ≤ C :=
    hK.exists_bound_of_continuousOn
      (ha.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using hbound
  refine ⟨∑ j ∈ Finset.range (k + 1), max 0 (C j), ?_⟩
  intro j hj x hx
  exact (hC j x hx).trans ((le_max_right _ _).trans
    (Finset.single_le_sum (fun i _ => le_max_left 0 (C i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))))

theorem MemWkpLocally.smooth_mul {O : Set E} {k : ℕ} {u a : E → ℝ}
    (hu : MemWkpLocally k u O) (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    MemWkpLocally k (fun x => a x * u x) O := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, huV⟩ := hu x hx
  obtain ⟨C, hC⟩ := exists_iteratedFDeriv_bound_on_compact ha (isCompact_closedBall x 1) k
  let W := V ∩ ball x 1
  have hW : IsOpen W := hV.inter isOpen_ball
  refine ⟨W, hW, ⟨hxV, mem_ball_self (by norm_num)⟩,
    inter_subset_left.trans hVO, ?_⟩
  exact MemWkp.smul_smooth_bounded k (by norm_num) hW ha
    (fun j hj y hy => hC j hj y (ball_subset_closedBall hy.2))
    (huV.mono_set (by norm_num) hW inter_subset_left)

theorem MemWkpLocally.weakPartial {O : Set E} {k : ℕ} {u g : E → ℝ}
    (hu : MemWkpLocally (k + 1) u O) (hg : MemWkpLocally 0 g O)
    {i : Fin d} (hweak : Weak.HasWeakPartialDeriv i g u O) :
    MemWkpLocally k g O := by
  intro x hx
  obtain ⟨U, hU, hxU, hUO, huU⟩ := hu x hx
  obtain ⟨V, hV, hxV, _, hgV⟩ := hg x hx
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hWO : W ⊆ O := inter_subset_left.trans hUO
  have huW := huU.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW inter_subset_left
  have hgW := hgV.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW inter_subset_right
  have hae : chosenWeakPartial' 2 i u W =ᵐ[volume.restrict W] g :=
    Weak.HasWeakPartialDeriv.ae_eq hW
      (chosenWeakPartial'_isWeakPartial_of_mem huW.memW1p i) (hweak.restrict hW hWO)
      ((chosenWeakPartial'_memLp_of_mem huW.memW1p i).locallyIntegrable (by norm_num))
      (hgW.memLp.locallyIntegrable (by norm_num))
  exact ⟨W, hW, ⟨hxU, hxV⟩, hWO,
    (MemWkp_congr_ae (by norm_num) hW hae).mp (huW.chosenWeakPartial_mem i)⟩

theorem memWkpLocally_succ_of_weakDerivatives {O : Set E} (hO : IsOpen O)
    {k : ℕ} {u : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemWkpLocally 0 u O) (hp : ∀ i, MemWkpLocally k (p i) O)
    (hweak : ∀ i, Weak.HasWeakPartialDeriv i (p i) u O) :
    MemWkpLocally (k + 1) u O := by
  intro x hx
  obtain ⟨U, hU, hxU, hUO, huU⟩ := hu x hx
  obtain ⟨V, hV, hxV, _, hpV⟩ := MemWkpLocally.exists_common_neighborhood hO hp hx
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hWO : W ⊆ O := inter_subset_left.trans hUO
  refine ⟨W, hW, ⟨hxU, hxV⟩, hWO, ?_⟩
  exact memWkp_succ_of_weakDerivatives hW (by norm_num)
    ((huU.mono_set (by norm_num) hW inter_subset_left).memLp)
    (fun i => (hpV i).mono_set (by norm_num) hW inter_subset_right)
    (fun i => (hweak i).restrict hW hWO)

theorem memWkpLocally_zero_iff_compact_memLp {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} :
    MemWkpLocally 0 u O ↔ ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K) :=
  local_memLp_iff_compact_memLp hO

theorem memWkpLocally_zero_of_compact_memLp {O : Set E} (hO : IsOpen O)
    {u : E → ℝ}
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K)) :
    MemWkpLocally 0 u O :=
  (memWkpLocally_zero_iff_compact_memLp hO).mpr hu

theorem MemWkpLocally.compact_memLp {O : Set E} {k : ℕ} {u : E → ℝ}
    (hu : MemWkpLocally k u O) :
    ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K) :=
  compact_memLp_of_local_memLp (hu.mono_order (Nat.zero_le k))

theorem MemWkpLocally.weakPartial_of_compact_memLp {O : Set E} (hO : IsOpen O)
    {k : ℕ} {u g : E → ℝ} (hu : MemWkpLocally (k + 1) u O)
    (hg : ∀ K, IsCompact K → K ⊆ O → MemLp g 2 (volume.restrict K))
    {i : Fin d} (hweak : Weak.HasWeakPartialDeriv i g u O) :
    MemWkpLocally k g O :=
  hu.weakPartial (memWkpLocally_zero_of_compact_memLp hO hg) hweak

theorem memWkpLocally_succ_of_compact_memLp_weakDerivatives {O : Set E}
    (hO : IsOpen O) {k : ℕ} {u : E → ℝ} {p : Fin d → E → ℝ}
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i, MemWkpLocally k (p i) O)
    (hweak : ∀ i, Weak.HasWeakPartialDeriv i (p i) u O) :
    MemWkpLocally (k + 1) u O :=
  memWkpLocally_succ_of_weakDerivatives hO
    (memWkpLocally_zero_of_compact_memLp hO hu) hp hweak

end Poincare.Analysis.Elliptic
