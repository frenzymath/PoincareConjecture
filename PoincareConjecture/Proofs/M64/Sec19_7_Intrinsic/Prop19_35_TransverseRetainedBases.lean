import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TangentContactsNull











noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix ENNReal

namespace PoincareConjecture






theorem m64Intrinsic_exists_transverse_retained_bases
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ∃ Z : Set ℝ, MeasurableSet Z ∧ Z ⊆ S ∧ Z =ᵐ[volume] S ∧
      (∀ w : ℝ → ℝ≥0∞, (∫⁻ a in Z, w a) = ∫⁻ a in S, w a) ∧
      (∀ w : ℝ → ℝ, (∫ a in Z, w a) = ∫ a in S, w a) ∧
      ∀ a ∈ Z, ∀ t s : ℝ, e !₂[a, t] = target s →
        Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) →
        LinearIndependent ℝ
          (![deriv target s, fderiv ℝ e !₂[a, t] !₂[0, 1]] :
            Fin 2 → AnnulusCoordinates) := by
  let Bad : Set ℝ := {a : ℝ | ∃ t s : ℝ,
    e !₂[a, t] = target s ∧
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) ∧
    ¬ LinearIndependent ℝ
      (![deriv target s, fderiv ℝ e !₂[a, t] !₂[0, 1]] :
        Fin 2 → AnnulusCoordinates)}
  have hBad : volume Bad = 0 :=
    m64Intrinsic_curve_tangent_bases_null e he htarget
  obtain ⟨E, hBadE, hE, hE0⟩ := exists_measurable_superset_of_null hBad
  let Z := S \ E
  have hZS : Z =ᵐ[volume] S := sdiff_null_ae_eq_self hE0
  have hrestrict : volume.restrict Z = volume.restrict S :=
    Measure.restrict_congr_set hZS
  refine ⟨Z, hS.diff hE, sdiff_subset, hZS, ?_, ?_, ?_⟩
  · intro w
    rw [hrestrict]
  · intro w
    rw [hrestrict]
  · intro a ha t s hcontact hinj
    change a ∈ S \ E at ha
    by_contra hind
    have haBad : a ∈ Bad := ⟨t, s, hcontact, hinj, hind⟩
    exact ha.2 (hBadE haBad)

end PoincareConjecture
