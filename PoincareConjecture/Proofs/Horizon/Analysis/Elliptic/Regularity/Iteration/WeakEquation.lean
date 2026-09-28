import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.TestCalculus

noncomputable section

open Set MeasureTheory Function Filter Topology
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Elliptic.Iteration

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def WeakEquation (O : Set E) (F : Fin n → E → ℝ) (f : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
    (∫ x in O, ∑ i, F i x * partialDeriv i φ x) = ∫ x in O, f x * φ x

theorem WeakEquation.restrict {O V : Set E} (hVO : V ⊆ O)
    {F : Fin n → E → ℝ} {f : E → ℝ} (heq : WeakEquation O F f) :
    WeakEquation V F f := by
  intro φ hφ hφc hφV
  have hderivzero : ∀ i x, x ∉ V → partialDeriv i φ x = 0 := by
    intro i x hx
    exact image_eq_zero_of_notMem_tsupport
      (fun h => hx (hφV (tsupport_partial_subset i φ h)))
  have hφzero : ∀ x, x ∉ V → φ x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hφV h))
  have hraw := heq φ hφ hφc (hφV.trans hVO)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hderivzero _ x (fun hv => hx (hVO hv))]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hφzero x (fun hv => hx (hVO hv))])] at hraw
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hderivzero _ x hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hφzero x hx])]
  exact hraw

theorem WeakEquation.congr_flux {O : Set E}
    {F G : Fin n → E → ℝ} {f : E → ℝ}
    (heq : WeakEquation O F f)
    (hFG : ∀ i, F i =ᵐ[volume.restrict O] G i) :
    WeakEquation O G f := by
  intro φ hφ hφc hφO
  rw [← heq φ hφ hφc hφO]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hFG] with x hx
  exact Finset.sum_congr rfl (fun i _ => by rw [hx i])

theorem locallyIntegrable_finset_sum {ι : Type*} (s : Finset ι) {O : Set E}
    {f : ι → E → ℝ} (hf : ∀ i ∈ s, LocallyIntegrable (f i) (volume.restrict O)) :
    LocallyIntegrable (fun x => ∑ i ∈ s, f i x) (volume.restrict O) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (locallyIntegrable_zero : LocallyIntegrable
      (fun _ : E => (0 : ℝ)) (volume.restrict O))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem weakPartial_finset_sum {ι : Type*} (s : Finset ι) {O : Set E}
    {u g : ι → E → ℝ} {k : Fin n}
    (hu : ∀ i ∈ s, LocallyIntegrable (u i) (volume.restrict O))
    (hg : ∀ i ∈ s, LocallyIntegrable (g i) (volume.restrict O))
    (hweak : ∀ i ∈ s, Sobolev.Weak.HasWeakPartialDeriv k (g i) (u i) O) :
    Sobolev.Weak.HasWeakPartialDeriv k (fun x => ∑ i ∈ s, g i x)
      (fun x => ∑ i ∈ s, u i x) O := by
  intro φ hφ hφc hφO
  change (∫ x in O, (∑ i ∈ s, u i x) * partialDeriv k φ x) =
    -(∫ x in O, (∑ i ∈ s, g i x) * φ x)
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum s (fun i hi => integrable_mul_partial_test (hu i hi) hφ hφc k),
    integral_finsetSum s (fun i hi => integrable_mul_test (hg i hi) hφ hφc)]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i hi => hweak i hi φ hφ hφc hφO)

theorem WeakEquation.differentiate
    {O : Set E} {F G : Fin n → E → ℝ} {f g : E → ℝ} {k : Fin n}
    (heq : WeakEquation O F f)
    (hF : ∀ i, LocallyIntegrable (F i) (volume.restrict O))
    (hG : ∀ i, LocallyIntegrable (G i) (volume.restrict O))
    (hFG : ∀ i, Sobolev.Weak.HasWeakPartialDeriv k (G i) (F i) O)
    (hfg : Sobolev.Weak.HasWeakPartialDeriv k g f O) :
    WeakEquation O G g := by
  intro φ hφ hφc hφO
  have hDφ := contDiff_partial hφ k
  have hDφc := hasCompactSupport_partial hφc k
  have hDφO := (tsupport_partial_subset k φ).trans hφO
  have hbase := heq (partialDeriv k φ) hDφ hDφc hDφO
  have hrhs := hfg φ hφ hφc hφO
  change (∫ x in O, f x * partialDeriv k φ x) = -(∫ x in O, g x * φ x) at hrhs
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_mul_partial_test (hF i) hDφ hDφc i)] at hbase
  have hterm : ∀ i, (∫ x in O, F i x * partialDeriv i (partialDeriv k φ) x) =
      -(∫ x in O, G i x * partialDeriv i φ x) := by
    intro i
    rw [partial_comm hφ i k]
    exact hFG i (partialDeriv i φ) (contDiff_partial hφ i)
      (hasCompactSupport_partial hφc i) ((tsupport_partial_subset i φ).trans hφO)
  simp_rw [hterm] at hbase
  rw [Finset.sum_neg_distrib, hrhs] at hbase
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_mul_partial_test (hG i) hφ hφc i)]
  exact neg_injective hbase

theorem WeakEquation.remove_flux
    {O : Set E} {F H S : Fin n → E → ℝ} {f : E → ℝ}
    (heq : WeakEquation O (fun i x => F i x + H i x) f)
    (hF : ∀ i, LocallyIntegrable (F i) (volume.restrict O))
    (hH : ∀ i, LocallyIntegrable (H i) (volume.restrict O))
    (hS : ∀ i, LocallyIntegrable (S i) (volume.restrict O))
    (hf : LocallyIntegrable f (volume.restrict O))
    (hHS : ∀ i, Sobolev.Weak.HasWeakPartialDeriv i (S i) (H i) O) :
    WeakEquation O F (fun x => f x + ∑ i, S i x) := by
  intro φ hφ hφc hφO
  have hbase := heq φ hφ hφc hφO
  have hFφ i := integrable_mul_partial_test (hF i) hφ hφc i
  have hHφ i := integrable_mul_partial_test (hH i) hφ hφc i
  have hSφ i := integrable_mul_test (hS i) hφ hφc
  have hHSeq i := hHS i φ hφ hφc hφO
  change ∀ i, (∫ x in O, H i x * partialDeriv i φ x) =
    -(∫ x in O, S i x * φ x) at hHSeq
  simp_rw [add_mul, Finset.sum_add_distrib] at hbase
  rw [integral_add (integrable_finsetSum _ (fun i _ => hFφ i))
    (integrable_finsetSum _ (fun i _ => hHφ i)),
    integral_finsetSum Finset.univ (fun i _ => hHφ i)] at hbase
  simp_rw [hHSeq] at hbase
  rw [Finset.sum_neg_distrib] at hbase
  simp_rw [add_mul, Finset.sum_mul]
  rw [integral_add (integrable_mul_test hf hφ hφc)
    (integrable_finsetSum _ (fun i _ => hSφ i)),
    integral_finsetSum Finset.univ (fun i _ => hSφ i)]
  linarith

end Poincare.Analysis.Elliptic.Iteration
