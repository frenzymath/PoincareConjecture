import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EnergyCutoffs
import Mathlib.Algebra.Order.Floor.Semiring











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}


noncomputable def translatedEnergyCutoff (e : StandardCylindricalEnd g) (j : ℕ) :
    StandardCapSpace → ℝ := endEnergyProfile ∘ fun x => endExhaustion e x - (j : ℝ)


theorem translatedEnergyCutoff_contDiff (e : StandardCylindricalEnd g) (j : ℕ) :
    ContDiff ℝ ∞ (translatedEnergyCutoff e j) :=
  endEnergyProfile.contDiff.comp
    ((contMDiff_iff_contDiff.mp (endExhaustion_contMDiff e)).sub contDiff_const)



theorem translatedEnergyCutoff_mem_Icc (e : StandardCylindricalEnd g) (j : ℕ)
    (x : StandardCapSpace) : translatedEnergyCutoff e j x ∈ Icc (0 : ℝ) 1 :=
  ⟨endEnergyProfile.nonneg, endEnergyProfile.le_one⟩



theorem translatedEnergyCutoff_eq_one (e : StandardCylindricalEnd g) (j : ℕ)
    {x : StandardCapSpace} (hx : endExhaustion e x - (j : ℝ) ∈ Icc (22 / 5 : ℝ) (28 / 5)) :
    translatedEnergyCutoff e j x = 1 := by
  apply endEnergyProfile.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |endExhaustion e x - (j : ℝ) - 5| ≤ 3 / 5
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]



theorem translatedEnergyCutoff_tsupport (e : StandardCylindricalEnd g) (j : ℕ) :
    tsupport (translatedEnergyCutoff e j) ⊆
      {x | endExhaustion e x ∈ Icc ((j : ℝ) + 41 / 10) ((j : ℝ) + 59 / 10)} := by
  intro x hx
  have hh := tsupport_comp_subset_preimage (endEnergyProfile : ℝ → ℝ)
    ((endExhaustion_contMDiff e).continuous.sub continuous_const) hx
  change endExhaustion e x - (j : ℝ) ∈ tsupport (endEnergyProfile : ℝ → ℝ) at hh
  rw [endEnergyProfile.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hh
  change |endExhaustion e x - (j : ℝ) - 5| ≤ 9 / 10 at hh
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> linarith



theorem translatedEnergyCutoff_hasCompactSupport (e : StandardCylindricalEnd g) (j : ℕ) :
    HasCompactSupport (translatedEnergyCutoff e j) :=
  (endExhaustion_sublevel_isCompact e ((j : ℝ) + 59 / 10)).of_isClosed_subset
    (isClosed_tsupport _) (fun _ hx => (translatedEnergyCutoff_tsupport e j hx).2)



theorem translatedEnergyCutoff_chart (e : StandardCylindricalEnd g) (j : ℕ)
    {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e) :
    translatedEnergyCutoff e j (endAxialTranslation e (j : ℝ) x) = endEnergyCutoff e x := by
  have hh := endExhaustion_translation_eq e (s := (j : ℝ) + 4)
    (by have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j; linarith) hx
  have hj : (j : ℝ) + 4 - 4 = j := by ring
  rw [hj] at hh
  exact congrArg endEnergyProfile hh



theorem translatedEnergyCutoff_localization (e : StandardCylindricalEnd g) (j : ℕ)
    {x : StandardCapSpace} (hx : x ∈ tsupport (translatedEnergyCutoff e j)) :
    ∃ y ∈ endReferenceRegion e, endAxialTranslation e (j : ℝ) y = x ∧
      endEnergyCutoff e y = translatedEnergyCutoff e j x := by
  have hh := translatedEnergyCutoff_tsupport e j hx
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  obtain ⟨z, _, hz, hrho⟩ := endExhaustion_large_coordinate e (by linarith [hh.1])
  let w : StandardCylinderSpace := (z.1, z.2 - (j : ℝ))
  have hw : w.2 ∈ Ioo (3 : ℝ) 5 := by
    dsimp only [w]
    constructor <;> linarith [hh.1, hh.2]
  have hy : e.coordinate w ∈ endReferenceRegion e := ⟨w, ⟨mem_univ _, hw⟩, rfl⟩
  have heq : endAxialTranslation e (j : ℝ) (e.coordinate w) = x := by
    rw [endAxialTranslation_coordinate e (j : ℝ) (by linarith [hw.1])]
    simpa only [w, sub_add_cancel, Prod.mk.eta] using hz
  refine ⟨e.coordinate w, hy, heq, ?_⟩
  rw [← heq, translatedEnergyCutoff_chart e j hy]



theorem energyCutoffs_plateau_cover (e : StandardCylindricalEnd g) (x : StandardCapSpace) :
    coreEnergyCutoff e x = 1 ∨ ∃ j : ℕ, translatedEnergyCutoff e j x = 1 := by
  by_cases hx : endExhaustion e x ≤ 5
  · exact Or.inl (coreEnergyCutoff_eq_one e hx)
  · right
    let j := Nat.floor (endExhaustion e x - 9 / 2)
    have hlo : (j : ℝ) ≤ endExhaustion e x - 9 / 2 := Nat.floor_le (by linarith)
    have hhi : endExhaustion e x - 9 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    refine ⟨j, translatedEnergyCutoff_eq_one e j ?_⟩
    constructor <;> linarith



theorem translatedEnergyCutoff_neighbors (e : StandardCylindricalEnd g) {j k : ℕ}
    {x : StandardCapSpace} (hj : x ∈ tsupport (translatedEnergyCutoff e j))
    (hk : x ∈ tsupport (translatedEnergyCutoff e k)) : j ≤ k + 1 ∧ k ≤ j + 1 := by
  have hjb := translatedEnergyCutoff_tsupport e j hj
  have hkb := translatedEnergyCutoff_tsupport e k hk
  have hjk : (j : ℝ) < (k : ℝ) + 2 := by linarith [hjb.1, hkb.2]
  have hkj : (k : ℝ) < (j : ℝ) + 2 := by linarith [hkb.1, hjb.2]
  have hjkn : j < k + 2 := by exact_mod_cast hjk
  have hkjn : k < j + 2 := by exact_mod_cast hkj
  omega



theorem translatedEnergyCutoff_core_neighbors (e : StandardCylindricalEnd g) {j : ℕ}
    {x : StandardCapSpace} (hj : x ∈ tsupport (translatedEnergyCutoff e j))
    (hc : x ∈ tsupport (coreEnergyCutoff e)) : j ≤ 1 := by
  have hjb := translatedEnergyCutoff_tsupport e j hj
  have hcb : endExhaustion e x ≤ 6 := coreEnergyCutoff_tsupport e hc
  have hjr : (j : ℝ) < 2 := by linarith [hjb.1]
  have hjn : j < 2 := by exact_mod_cast hjr
  omega

end PoincareConjecture.M34
