import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereAlphaEnergy_continuous (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    Continuous (fun alpha : ℝ => m60SphereAlphaEnergy g alpha f) := by
  have hb : Continuous (fun q : ℝ × UnitTwoSphere =>
      1 + 2 * m60SphereIntrinsicEnergy g f q.2) :=
    continuous_const.add (continuous_const.mul
      ((m60SphereIntrinsicEnergy_contMDiff g f hf).continuous.comp continuous_snd))
  have hc : Continuous (fun q : ℝ × UnitTwoSphere =>
      (1 + 2 * m60SphereIntrinsicEnergy g f q.2) ^ q.1) :=
    hb.rpow continuous_fst (fun q => Or.inl (by
      have := m60SphereIntrinsicEnergy_nonneg g f q.2
      positivity))
  simpa only [m60SphereAlphaEnergy, Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (f := fun alpha p => (1 + 2 * m60SphereIntrinsicEnergy g f p) ^ alpha)
      (μ := m60RoundSphereMetric.volumeMeasure) hc (s := univ) isCompact_univ)

theorem m60SphereAlphaEnergy_normalized_tendsto (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    {alpha : ℕ → ℝ} (ha : Tendsto alpha atTop (𝓝 1)) :
    Tendsto (fun j => (m60SphereAlphaEnergy g (alpha j) f - 4 * Real.pi) / 2)
      atTop (𝓝 (m60SphereEnergy g f)) := by
  have h := (((m60SphereAlphaEnergy_continuous g f hf).tendsto 1).comp ha).sub_const
    (4 * Real.pi)
  have h' := h.div_const 2
  rw [m60SphereAlphaEnergy_one g f hf] at h'
  have heq : (4 * Real.pi + 2 * m60SphereEnergy g f - 4 * Real.pi) / 2 =
      m60SphereEnergy g f := by ring
  rw [heq] at h'
  exact h'

theorem m60PerturbedMinimizers_energy_tendsto (g : RiemannianMetric n M)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (ha : Tendsto alpha atTop (𝓝 1)) (ha1 : ∀ j, 1 ≤ alpha j)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hmin : ∀ j (h : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) ∞ h →
      ¬ IsNullHomotopicSphere h →
      m60SphereAlphaEnergy g (alpha j) (f j) ≤ m60SphereAlphaEnergy g (alpha j) h) :
    let I := sInf (m60SphereEnergy g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) ∞ h ∧ ¬ IsNullHomotopicSphere h})
    Tendsto (fun j => (m60SphereAlphaEnergy g (alpha j) (f j) - 4 * Real.pi) / 2)
      atTop (𝓝 I) ∧
      Tendsto (fun j => m60SphereEnergy g (f j)) atTop (𝓝 I) := by
  let S : Set (UnitTwoSphere → M) :=
    {h | ContMDiff (𝓡 2) (𝓡 n) ∞ h ∧ ¬ IsNullHomotopicSphere h}
  let I := sInf (m60SphereEnergy g '' S)
  let J : ℕ → ℝ := fun j =>
    (m60SphereAlphaEnergy g (alpha j) (f j) - 4 * Real.pi) / 2
  change Tendsto J atTop (𝓝 I) ∧
    Tendsto (fun j => m60SphereEnergy g (f j)) atTop (𝓝 I)
  have hS : S.Nonempty := ⟨f 0, hf 0, hn 0⟩
  have hb : BddBelow (m60SphereEnergy g '' S) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, -, rfl⟩
    exact m60SphereEnergy_nonneg g h
  have hlow (j : ℕ) : I ≤ m60SphereEnergy g (f j) :=
    csInf_le hb ⟨f j, ⟨hf j, hn j⟩, rfl⟩
  have hupp (j : ℕ) : m60SphereEnergy g (f j) ≤ J j := by
    have hh := m60SphereEnergy_le_alphaEnergy g (ha1 j) (f j) (hf j)
    dsimp only [J]
    linarith
  have hJ : Tendsto J atTop (𝓝 I) := by
    apply tendsto_order.mpr
    constructor
    · intro a haI
      exact Eventually.of_forall fun j => haI.trans_le ((hlow j).trans (hupp j))
    · intro b hIb
      obtain ⟨r, hr, hrb⟩ := exists_lt_of_csInf_lt (hS.image (m60SphereEnergy g)) hIb
      obtain ⟨h, hh, rfl⟩ := hr
      have ht := m60SphereAlphaEnergy_normalized_tendsto g h hh.1 ha
      filter_upwards [ht.eventually (gt_mem_nhds hrb)] with j hj
      have hm := hmin j h hh.1 hh.2
      dsimp only [J]
      linarith
  exact ⟨hJ, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJ hlow hupp⟩

end PoincareConjecture
