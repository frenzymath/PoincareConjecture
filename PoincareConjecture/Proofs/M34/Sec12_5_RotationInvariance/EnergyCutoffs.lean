import PoincareConjecture.Proofs.M34.Standard.TranslatedEndCharts
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



noncomputable def endEnergyProfile : ContDiffBump (5 : ℝ) where
  rIn := 3 / 5
  rOut := 9 / 10
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num



noncomputable def endEnergyCutoff (e : StandardCylindricalEnd g) : StandardCapSpace → ℝ :=
  endEnergyProfile ∘ endExhaustion e



noncomputable def coreEnergyCutoff (e : StandardCylindricalEnd g)
    (x : StandardCapSpace) : ℝ := Real.smoothTransition (6 - endExhaustion e x)



theorem energyCutoffs_contDiff (e : StandardCylindricalEnd g) :
    ContDiff ℝ ∞ (endEnergyCutoff e) ∧ ContDiff ℝ ∞ (coreEnergyCutoff e) := by
  have hrho := contMDiff_iff_contDiff.mp (endExhaustion_contMDiff e)
  exact ⟨endEnergyProfile.contDiff.comp hrho,
    Real.smoothTransition.contDiff.comp (contDiff_const.sub hrho)⟩



theorem energyCutoffs_mem_Icc (e : StandardCylindricalEnd g) (x : StandardCapSpace) :
    endEnergyCutoff e x ∈ Icc (0 : ℝ) 1 ∧ coreEnergyCutoff e x ∈ Icc (0 : ℝ) 1 :=
  ⟨⟨endEnergyProfile.nonneg, endEnergyProfile.le_one⟩,
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩



theorem endEnergyCutoff_eq_one (e : StandardCylindricalEnd g) {x : StandardCapSpace}
    (hx : endExhaustion e x ∈ Icc (22 / 5 : ℝ) (28 / 5)) : endEnergyCutoff e x = 1 := by
  apply endEnergyProfile.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |endExhaustion e x - 5| ≤ 3 / 5
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]



theorem coreEnergyCutoff_eq_one (e : StandardCylindricalEnd g) {x : StandardCapSpace}
    (hx : endExhaustion e x ≤ 5) : coreEnergyCutoff e x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)



theorem endEnergyCutoff_tsupport (e : StandardCylindricalEnd g) :
    tsupport (endEnergyCutoff e) ⊆
      {x | endExhaustion e x ∈ Icc (41 / 10 : ℝ) (59 / 10)} := by
  intro x hx
  have hh := tsupport_comp_subset_preimage (endEnergyProfile : ℝ → ℝ)
    (endExhaustion_contMDiff e).continuous hx
  change endExhaustion e x ∈ tsupport (endEnergyProfile : ℝ → ℝ) at hh
  rw [endEnergyProfile.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hh
  change |endExhaustion e x - 5| ≤ 9 / 10 at hh
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> linarith



theorem coreEnergyCutoff_tsupport (e : StandardCylindricalEnd g) :
    tsupport (coreEnergyCutoff e) ⊆ {x | endExhaustion e x ≤ 6} := by
  apply closure_minimal
  · intro x hx
    by_contra hle
    change ¬endExhaustion e x ≤ 6 at hle
    have hz : coreEnergyCutoff e x = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith [not_le.mp hle])
    exact hx hz
  · exact isClosed_le (endExhaustion_contMDiff e).continuous continuous_const



theorem energyCutoffs_hasCompactSupport (e : StandardCylindricalEnd g) :
    HasCompactSupport (endEnergyCutoff e) ∧ HasCompactSupport (coreEnergyCutoff e) := by
  constructor
  · exact (endExhaustion_sublevel_isCompact e (59 / 10)).of_isClosed_subset
      (isClosed_tsupport _) (fun x hx => (endEnergyCutoff_tsupport e hx).2)
  · exact (endExhaustion_sublevel_isCompact e 6).of_isClosed_subset
      (isClosed_tsupport _) (coreEnergyCutoff_tsupport e)



theorem endExhaustion_large_coordinate (e : StandardCylindricalEnd g) {x : StandardCapSpace}
    (hx : 3 < endExhaustion e x) :
    ∃ z : StandardCylinderSpace, 2 < z.2 ∧ e.coordinate z = x ∧
      endExhaustion e x = 1 + z.2 := by
  have hcar : x ∈ e.carrier := by
    by_contra hn
    have heq : endExhaustion e x = 1 := by simp [endExhaustion, hn]
    linarith
  have hz := e.inverse_domain x hcar
  have hform := endExhaustion_coordinate e hz
  rw [e.coordinate_right_inverse hcar] at hform
  have hle : endExhaustion e x ≤ 1 + (e.inverse x).2 := by
    rw [hform]
    have hb := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one ((e.inverse x).2 - 1)) hz
    linarith
  have htwo : 2 < (e.inverse x).2 := by linarith
  refine ⟨e.inverse x, htwo, e.coordinate_right_inverse hcar, ?_⟩
  have heq := endExhaustion_coordinate_of_two_le e htwo.le
  rwa [e.coordinate_right_inverse hcar] at heq



theorem endEnergyCutoff_tsupport_subset_region (e : StandardCylindricalEnd g) :
    tsupport (endEnergyCutoff e) ⊆ endReferenceRegion e := by
  intro x hx
  have hh := endEnergyCutoff_tsupport e hx
  obtain ⟨z, _, hz, heq⟩ := endExhaustion_large_coordinate e (by linarith [hh.1])
  refine ⟨z, ⟨mem_univ _, ?_⟩, hz⟩
  constructor <;> linarith [hh.1, hh.2]

end PoincareConjecture.M34
