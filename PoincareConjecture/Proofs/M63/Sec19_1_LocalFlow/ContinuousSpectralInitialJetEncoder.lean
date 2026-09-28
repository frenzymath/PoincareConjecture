import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialCoordinateEncoder
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothSpectralInitialOrbit
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ContDiff

universe v

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle L, W)
local notation "J" => ((X × X) × X) × ℝ
local notation "S" => State ((ℤ × Fin 2) × ι)

theorem exists_continuous_vectorPeriodic_initialJet_encoder :
    ∃ A : J →L[ℝ] S, ∀ p : J,
      (∀ x : ℝ,
        HasDerivAt (fun y : ℝ => p.1.1.1 (y : AddCircle L))
          (p.1.1.2 (x : AddCircle L)) x ∧
        HasDerivAt (fun y : ℝ => p.1.1.2 (y : AddCircle L))
          (p.1.2 (x : AddCircle L)) x) →
      (∀ z : AddCircle L,
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) (A p) z) =
          p.1.1.1 z ∧
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) (A p) z) =
          p.1.1.2 z) ∧
      (ContDiff ℝ ∞ (fun x : ℝ => p.1.1.1 (x : AddCircle L)) →
        ContDiff ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (A p))) := by
  classical
  let E : W ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let T := E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)
  let C (i : ι) : W →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp E.toContinuousLinearMap
  let P (i : ι) : X →L[ℝ] C(AddCircle L, ℝ) :=
    (C i).compLeftContinuous ℝ (AddCircle L)
  let Q0 : J →L[ℝ] X := (ContinuousLinearMap.fst ℝ X X).comp
    ((ContinuousLinearMap.fst ℝ (X × X) X).comp
      (ContinuousLinearMap.fst ℝ ((X × X) × X) ℝ))
  let Q2 : J →L[ℝ] X := (ContinuousLinearMap.snd ℝ (X × X) X).comp
    (ContinuousLinearMap.fst ℝ ((X × X) × X) ℝ)
  let A0 : (X × X) →L[ℝ] S :=
    (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => realPeriodicH2Encode.comp ((P i).prodMap (P i))))
  let A : J →L[ℝ] S := A0.comp (Q0.prod Q2)
  have hAi (p : J) (i : ι) : lpFinitePiEquiv ℝ (A p) i =
      realPeriodicH2Encode (P i p.1.1.1, P i p.1.2) := by
    change lpFinitePiEquiv ℝ ((lpFinitePiEquiv ℝ).symm
      (fun j => realPeriodicH2Encode (P j p.1.1.1, P j p.1.2))) i = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨A, ?_⟩
  intro p hp
  have hs (i : ι) := realPeriodicH2Encode_spec (P i p.1.1.1)
    (P i p.1.1.2) (P i p.1.2)
    (fun x => (C i).hasFDerivAt.comp_hasDerivAt x (hp x).1)
    (fun x => (C i).hasFDerivAt.comp_hasDerivAt x (hp x).2)
  have hcoeff (i : ι) (n : ℤ) :
      complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (A p) i) n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L)
            (P i p.1.1.1)) n := by
    rw [hAi]
    exact (hs i).1 n
  have hzero : vectorPeriodicJet (L := L) 1 0 (by omega) (A p) = T p.1.1.1 := by
    ext z i
    change realPeriodicJet (L := L) 1 0 (by omega)
      (lpFinitePiEquiv ℝ (A p) i) z = E (p.1.1.1 z) i
    rw [hAi, (hs i).2.1]
    rfl
  have hzeroW (z : AddCircle L) :
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) (A p) z) = p.1.1.1 z := by
    rw [hzero]
    exact E.symm_apply_apply (p.1.1.1 z)
  refine ⟨?_, ?_⟩
  · intro z
    refine ⟨hzeroW z, ?_⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hd := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_vectorPeriodicJet (L := L) (k := 1) (j := 0) (by omega) (A p) x)
    change HasDerivAt (fun y : ℝ => E.symm
      (vectorPeriodicJet (L := L) 1 0 (by omega) (A p) (y : AddCircle L))) _ x at hd
    have hf : (fun y : ℝ => E.symm
        (vectorPeriodicJet (L := L) 1 0 (by omega) (A p) (y : AddCircle L))) =
        fun y : ℝ => p.1.1.1 (y : AddCircle L) := funext (fun y => hzeroW (y : AddCircle L))
    rw [hf] at hd
    exact hd.unique (hp x).1
  · intro hsm
    have hsm' : ContDiff ℝ ∞ (fun x : ℝ => T p.1.1.1 (x : AddCircle L)) :=
      E.toContinuousLinearMap.contDiff.comp hsm
    obtain ⟨w, hw, _hrec, _hbase, horbit⟩ :=
      exists_smooth_vectorPeriodic_spectral_initial_state (T p.1.1.1) hsm'
    have heq : A p = w := by
      apply (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).injective
      funext i
      apply complexLpRealEquiv.symm.injective
      apply lp.ext
      funext n
      exact (hcoeff i n).trans (hw i n).symm
    rw [heq]
    exact horbit

end PoincareConjecture.M63
