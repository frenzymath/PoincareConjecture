import PoincareConjecture.Proofs.M08.PathEnergy
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.UniformSpace.Cauchy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral NNReal

namespace PoincareConjecture.M08

theorem exists_continuous_endpoint_of_lipschitz {X : Type*} [MetricSpace X]
    [CompleteSpace X] {a b : ℝ} (hab : a < b) (f : ℝ → X) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Ioc a b)) :
    ∃ g : ℝ → X, ContinuousOn g (Icc a b) ∧ EqOn g f (Ioc a b) ∧
      LipschitzOnWith L g (Icc a b) := by
  have hclosure : closure (Ioc a b) = Icc a b := closure_Ioc hab.ne
  have hlim (x : ℝ) (hx : x ∈ Icc a b) : ∃ y, Tendsto f (𝓝[Ioc a b] x) (𝓝 y) := by
    have hx' : x ∈ closure (Ioc a b) := by rwa [hclosure]
    haveI : NeBot (𝓝[Ioc a b] x) := mem_closure_iff_nhdsWithin_neBot.mp hx'
    apply cauchy_map_iff_exists_tendsto.mp
    exact (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hf.uniformContinuousOn
      inf_le_right
  let g := extendFrom (Ioc a b) f
  have hgc : ContinuousOn g (Icc a b) :=
    continuousOn_extendFrom (by rw [hclosure]) hlim
  have hgeq : EqOn g f (Ioc a b) := extendFrom_extends hf.continuousOn
  refine ⟨g, hgc, hgeq, ?_⟩
  have hLip : LipschitzOnWith L g (Ioc a b) := by
    intro x hx y hy
    rw [hgeq hx, hgeq hy]
    exact hf hx hy
  rw [← hclosure] at hgc ⊢
  exact hLip.closure hgc

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem lipschitzOnWith_of_referenceSpeed_bound [ConnectedSpace M] [T3Space M]
    (g : RiemannianMetric n M) {a b L : ℝ} (hL : 0 ≤ L) {U : Set ℝ}
    (hU : IsOpen U) (hIU : Ioc a b ⊆ U) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α U)
    (hbound : ∀ s ∈ Ioc a b, referenceSpeedSq g α s ≤ L) :
    letI : MetricSpace M := referenceMetricSpace g
    LipschitzOnWith ⟨Real.sqrt L, Real.sqrt_nonneg _⟩ α (Ioc a b) := by
  letI : MetricSpace M := referenceMetricSpace g
  have hordered (s : ℝ) (hs : s ∈ Ioc a b) (t : ℝ) (ht : t ∈ Ioc a b)
      (hst : s ≤ t) : dist (α s) (α t) ≤ Real.sqrt L * (t - s) := by
    rcases hst.eq_or_lt with heq | hst
    · subst t
      simp only [dist_self, sub_self, mul_zero, le_refl]
    have hsub : Icc s t ⊆ Ioc a b := fun r hr ↦ ⟨hs.1.trans_le hr.1, hr.2.trans ht.2⟩
    have hsubU := hsub.trans hIU
    have hqc := (referenceSpeedSq_continuousOn g hU hα).mono hsubU
    have hE : IntervalIntegrable (referenceSpeedSq g α) volume s t :=
      hqc.intervalIntegrable_of_Icc hst.le
    have henergy : (∫ r in s..t, referenceSpeedSq g α r) ≤ L * (t - s) := by
      calc
        _ ≤ ∫ _r in s..t, L := intervalIntegral.integral_mono_on hst.le hE
          intervalIntegrable_const (fun r hr ↦ hbound r (hsub hr))
        _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
    have h := dist_le_sqrt_energy g hst (hα.continuousOn.mono hsubU)
      (hα.mono (Ioo_subset_Icc_self.trans hsubU)) hE henergy
      s ⟨le_rfl, hst.le⟩ t ⟨hst.le, le_rfl⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hst.le), Real.sqrt_mul hL, mul_assoc,
      ← pow_two, Real.sq_sqrt (sub_nonneg.mpr hst.le)] at h
    exact h
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  change dist (α s) (α t) ≤ Real.sqrt L * dist s t
  rcases le_total s t with hst | hts
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using
      hordered s hs t ht hst
  · simpa only [dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)] using
      hordered t ht s hs hts

end PoincareConjecture.M08
