import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarIntegerCoverArea













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ




def scalarAngularCuts : Set Cover := ⋃ n : ℤ, Ioo (1 : ℝ) 2 ×ˢ {(n : ℝ)}




theorem scalarAngularCuts_measurable : MeasurableSet scalarAngularCuts :=
  MeasurableSet.iUnion fun n => measurableSet_Ioo.prod (measurableSet_singleton (n : ℝ))




theorem scalarAngularCuts_subset : scalarAngularCuts ⊆ scalarCoverStrip := by
  rintro z ⟨_, ⟨n, rfl⟩, hz⟩
  exact hz.1




theorem scalarAngularCuts_measure_zero : volume scalarAngularCuts = 0 := by
  apply measure_iUnion_null
  intro n
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp





theorem scalarAngularCuts_image_measure_zero {f : Cover → Cover}
    (hd : ∀ z ∈ scalarCoverStrip, DifferentiableAt ℝ f z) :
    volume (f '' scalarAngularCuts) = 0 := by
  have h := addHaar_image_le_lintegral_abs_det_fderiv volume scalarAngularCuts_measurable
    (fun z hz => (hd z (scalarAngularCuts_subset hz)).hasFDerivAt.hasFDerivWithinAt)
  have hzero : volume.restrict scalarAngularCuts = 0 :=
    Measure.restrict_eq_zero.mpr scalarAngularCuts_measure_zero
  rw [hzero, lintegral_zero_measure] at h
  exact le_antisymm h zero_le




theorem scalarNormalizedCoverMap_sub_int {H : Plane → ℝ} {V : Cover → ℝ}
    {P : ℝ} (hP : P ≠ 0)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    {z : Cover} (hz : z ∈ scalarCoverStrip) (n : ℤ) :
    scalarNormalizedCoverMap H V P (z - (0, (n : ℝ))) =
      scalarNormalizedCoverMap H V P z - (0, (n : ℝ)) := by
  let F := scalarNormalizedCoverMap H V P
  have hper : Function.Periodic (fun t : ℝ => F (z.1, t) - (0, t)) 1 := by
    intro t
    have h := scalarNormalizedCoverMap_deck (H := H) hP hdeck
      (show (z.1, t) ∈ scalarCoverStrip from hz)
    simp only [Prod.mk_add_mk, add_zero] at h
    change F (z.1, t + 1) = F (z.1, t) + (0, 1) at h
    dsimp only
    rw [h]
    ext <;> simp
  have h : F (z.1, z.2 - (n : ℝ) * 1) - (0, z.2 - (n : ℝ) * 1) =
      F (z.1, z.2) - (0, z.2) := hper.sub_int_mul_eq n
  simp only [mul_one] at h
  change F (z - (0, (n : ℝ))) = F z - (0, (n : ℝ))
  rw [show z - (0, (n : ℝ)) = (z.1, z.2 - (n : ℝ)) by ext <;> simp]
  apply Prod.ext
  · have h0 := congrArg Prod.fst h
    simpa only [Prod.fst_sub, sub_zero, Prod.mk.eta] using h0
  · have h1 := congrArg Prod.snd h
    simp only [Prod.snd_sub] at h1
    change (F (z.1, z.2 - (n : ℝ))).2 = (F z).2 - (n : ℝ)
    linarith

end PoincareConjecture.M64Uniformization
