import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralSpatialJets
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]
  {T : ℝ} (hT : 0 ≤ T) (w : State ((ℤ × Fin 2) × ι))
  (F0 : ForcingSpace ((ℤ × Fin 2) × ι) T)

noncomputable def initialResponseCurve : ℝ → ℝ → EuclideanSpace ℝ ι :=
  fun t x => WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega)
    (initialResponseTrace (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1)
      w hT F0 (projIcc 0 T hT t)) (x : AddCircle L))

theorem initialResponseCurve_spec :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let V := initialResponseTrace lambda w hT F0
    let q := initialResponseCurve (L := L) hT w F0
    Continuous (Function.uncurry q) ∧
      (∀ t, Function.Periodic (q t) L) ∧
      (∀ x, q 0 x = WithLp.toLp 2
        (vectorPeriodicJet (L := L) 1 0 (by omega) w (x : AddCircle L))) ∧
      ∀ (t x : ℝ), HasDerivAt (q t) (WithLp.toLp 2
        (vectorPeriodicJet (L := L) 1 1 (by omega)
          (V (projIcc 0 T hT t)) (x : AddCircle L))) x := by
  dsimp only
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := initialResponseTrace lambda w hT F0
  let E : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let D := vectorPeriodicJet (L := L) (ι := ι) 1 0 (by omega)
  have hcont : Continuous (fun z : ℝ × ℝ =>
      D (V (projIcc 0 T hT z.1)) (z.2 : AddCircle L)) :=
    continuous_eval.comp
      ((D.continuous.comp (V.continuous.comp
        (continuous_projIcc.comp continuous_fst))).prodMk
          ((AddCircle.continuous_mk' L).comp continuous_snd))
  refine ⟨E.continuous.comp hcont, ?_, ?_, ?_⟩
  · intro t x
    change E (D (V (projIcc 0 T hT t)) ((x + L : ℝ) : AddCircle L)) = _
    rw [AddCircle.coe_add_period]
    rfl
  · intro x
    unfold initialResponseCurve
    rw [projIcc_left, (initialResponseTrace_spec lambda w hT F0).1]
  · intro t x
    exact E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_vectorPeriodicJet (L := L) (k := 1) (j := 0) (by omega)
        (V (projIcc 0 T hT t)) x)

theorem initialResponseCurve_spatial_jets :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let q := initialResponseCurve (L := L) hT w F0
    ContDiffAt ℝ ∞ (fun s : ℝ => initialResponseTrace lambda
      (vectorPeriodicSpectralTranslation (L := L) s w) hT
      ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F0)) 0 →
    (∀ t : ℝ, ContDiff ℝ ∞ (q t)) ∧
      ∀ k : ℕ, ∃ J : C(Icc (0 : ℝ) T, C(AddCircle L, EuclideanSpace ℝ ι)),
        ∀ (t : Icc (0 : ℝ) T) (x : ℝ),
          iteratedDeriv k (q (t : ℝ)) x = J t (x : AddCircle L) := by
  dsimp only
  intro horbit
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := initialResponseTrace lambda w hT F0
  let E : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let P := E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)
  obtain ⟨hspace, hjets⟩ := initialResponseTrace_spatial_jets (L := L) hT w F0 horbit
  constructor
  · intro t
    exact E.contDiff.comp (hspace (projIcc 0 T hT t))
  · intro k
    obtain ⟨J, hJ⟩ := hjets k
    refine ⟨⟨fun t => P (J t), P.continuous.comp J.continuous⟩, ?_⟩
    intro t x
    have hq : initialResponseCurve (L := L) hT w F0 (t : ℝ) =
        E.toContinuousLinearMap ∘ (fun y : ℝ =>
          vectorPeriodicJet (L := L) 1 0 (by omega) (V t) (y : AddCircle L)) := by
      funext y
      simp only [initialResponseCurve, projIcc_val]
      rfl
    rw [hq, iteratedDeriv_comp_clm E.toContinuousLinearMap k
      ((hspace t).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)), hJ]
    rfl

end PoincareConjecture.M63
