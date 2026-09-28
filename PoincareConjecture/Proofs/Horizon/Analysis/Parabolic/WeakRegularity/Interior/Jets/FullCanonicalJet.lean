




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.TimeSpatialJetAlgebra









open Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

def canonicalDirection {n : ℕ} (i : Fin (n + 1)) : Spacetime n :=
  if h : i.val < n then spatialDirection ⟨i.val, h⟩ else (0, 1)

@[simp] theorem canonicalDirection_castSucc {n : ℕ} (i : Fin n) :
    canonicalDirection i.castSucc = spatialDirection i := by
  simp only [canonicalDirection, Fin.val_castSucc, dif_pos i.isLt]

@[simp] theorem canonicalDirection_last {n : ℕ} :
    canonicalDirection (Fin.last n) = (0, 1) := by
  simp only [canonicalDirection, Fin.val_last, lt_self_iff_false, dite_false]


def HasCanonicalL2Jet {n : ℕ} (U : Set (Spacetime n)) :
    ℕ → (Spacetime n → ℝ) → Prop
  | 0, u => MemLp u 2 (volume.restrict U)
  | k + 1, u => MemLp u 2 (volume.restrict U) ∧
      ∃ g : Fin (n + 1) → Spacetime n → ℝ,
        (∀ i, HasCanonicalL2Jet U k (g i)) ∧
        ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ U →
          (∫ y in U, φ y * g i y) =
            -(∫ y in U, fderiv ℝ φ y (canonicalDirection i) * u y)

theorem HasCanonicalL2Jet.memLp
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasCanonicalL2Jet U k u) : MemLp u 2 (volume.restrict U) := by
  cases k with
  | zero => exact hu
  | succ k => exact hu.1

theorem HasCanonicalL2Jet.locallyIntegrableOn
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasCanonicalL2Jet U k u) : LocallyIntegrableOn u U volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hu.memLp.locallyIntegrable (by norm_num))

theorem HasCanonicalL2Jet.congr_ae
    {n k : ℕ} {U : Set (Spacetime n)} {u v : Spacetime n → ℝ}
    (hu : HasCanonicalL2Jet U k u) (huv : u =ᵐ[volume.restrict U] v) :
    HasCanonicalL2Jet U k v := by
  cases k with
  | zero => exact MemLp.ae_eq huv hu
  | succ k =>
    obtain ⟨hum, g, hg, hgw⟩ := hu
    refine ⟨MemLp.ae_eq huv hum, g, hg, ?_⟩
    intro i φ hφ hφc hφU
    rw [hgw i φ hφ hφc hφU]
    congr 1
    exact integral_congr_ae (huv.mono fun y hy =>
      congrArg (fun a => fderiv ℝ φ y (canonicalDirection i) * a) hy)

theorem HasCanonicalL2Jet.restrict
    {n k : ℕ} {U V : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasCanonicalL2Jet U k u) (hVU : V ⊆ U) : HasCanonicalL2Jet V k u := by
  induction k generalizing u with
  | zero => exact hu.mono_measure (Measure.restrict_mono hVU le_rfl)
  | succ k ih =>
    obtain ⟨hum, g, hg, hgw⟩ := hu
    refine ⟨hum.mono_measure (Measure.restrict_mono hVU le_rfl), g, fun i => ih (hg i), ?_⟩
    intro i φ hφ hφc hφV
    have hpair {ψ : Spacetime n → ℝ} (hψ : tsupport ψ ⊆ V)
        (a : Spacetime n → ℝ) : (∫ y in V, ψ y * a y) = ∫ y in U, ψ y * a y := by
      calc
        _ = ∫ y, ψ y * a y := setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ h)), zero_mul])
        _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hVU (hψ h))), zero_mul])).symm
    rw [hpair hφV, hpair (ψ := fun y => fderiv ℝ φ y (canonicalDirection i))
      ((tsupport_fderiv_apply_subset ℝ (canonicalDirection i)).trans hφV)]
    exact hgw i φ hφ hφc (hφV.trans hVU)

theorem HasCanonicalL2Jet.lower
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasCanonicalL2Jet U (k + 1) u) : HasCanonicalL2Jet U k u := by
  induction k generalizing u with
  | zero => exact hu.1
  | succ k ih =>
    obtain ⟨hum, g, hg, hgw⟩ := hu
    exact ⟨hum, g, fun i => ih (hg i), hgw⟩

theorem HasCanonicalL2Jet.of_le
    {n j k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasCanonicalL2Jet U k u) (hjk : j ≤ k) : HasCanonicalL2Jet U j u := by
  induction hjk with
  | refl => exact hu
  | @step k hjk ih => exact ih hu.lower

theorem HasTimeSpatialL2Jet.canonical
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U k k u) (hU : IsOpen U) :
    HasCanonicalL2Jet U k u := by
  induction k generalizing u with
  | zero => exact hu.memLp
  | succ k ih =>
    obtain ⟨g, hg, hgw⟩ := hu.exists_spatial_derivatives hU
    obtain ⟨hus, T, hT, hTw⟩ := hu
    let G (i : Fin (n + 1)) : Spacetime n → ℝ :=
      if h : i.val < n then g ⟨i.val, h⟩ else T
    refine ⟨hus.memLp, G, ?_, ?_⟩
    · intro i
      dsimp only [G]
      split_ifs with hi
      · exact ih (hg ⟨i.val, hi⟩).lower_time
      · exact ih hT.lower_spatial
    · intro i φ hφ hφc hφU
      dsimp only [G, canonicalDirection]
      split_ifs with hi
      · exact hgw ⟨i.val, hi⟩ φ hφ hφc hφU
      · exact hTw φ hφ hφc hφU

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
