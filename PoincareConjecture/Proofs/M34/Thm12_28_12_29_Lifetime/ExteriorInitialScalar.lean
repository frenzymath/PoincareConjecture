import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.ExteriorInitialJets
import PoincareConjecture.Proofs.M34.Standard.PullbackCurvatureJetBound
import PoincareConjecture.Proofs.M10.ScalarBound











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34




theorem partialFlow_exists_exterior_initial_scalar_bound
    (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    (hL : F.lifetime < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T ∈ Ioo 0 F.lifetime,
      ∃ X : Set StandardCapSpace, IsCompact X ∧
        ∀ x ∉ X, |(F.flow.connection T).scalarCurvature x| ≤ 9 * K := by
  let e := g0.cylindrical_end
  obtain ⟨a, H, ha, hjet⟩ :=
    partialFlow_exists_exterior_initial_jet_bounds P E0 F e hL
  obtain ⟨K, hK, hcurvature⟩ :=
    curvatureDerivativeNorm_bound_of_pullback_jets 3 0 ha H
  refine ⟨K, hK, ?_⟩
  intro T hT
  obtain ⟨N, hN⟩ := hjet T hT
  let R : ℝ := 1 + (N : ℝ) + 9 / 2
  refine ⟨{x | endExhaustion e x ≤ R}, endExhaustion_sublevel_isCompact e R, ?_⟩
  intro x hx
  have hlarge : R < endExhaustion e x := lt_of_not_ge hx
  have hN0 := Nat.cast_nonneg (α := ℝ) N
  obtain ⟨z, _hz, hcoord, hrho⟩ := endExhaustion_large_coordinate e
    (by dsimp [R] at hlarge; linarith : 3 < endExhaustion e x)
  have hs : (N : ℝ) + 9 / 2 < z.2 := by dsimp [R] at hlarge; linarith
  let k : ℕ := ⌊z.2 - 9 / 2⌋₊
  have hs0 : 0 ≤ z.2 - 9 / 2 := by linarith
  have hk : N ≤ k := (Nat.le_floor_iff hs0).mpr (by linarith)
  have hr : z.2 - (k + 1 : ℕ) ∈ Icc (17 / 5 : ℝ) (23 / 5) := by
    have hlo := Nat.floor_le hs0
    have hhi := Nat.lt_floor_add_one (z.2 - 9 / 2)
    change (17 / 5 : ℝ) ≤ z.2 - (k + 1 : ℕ) ∧
      z.2 - (k + 1 : ℕ) ≤ 23 / 5
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [k]
    constructor <;> linarith
  let y := e.coordinate (z.1, z.2 - (k + 1 : ℕ))
  have hy : y ∈ endClosedSlab e (17 / 5) (23 / 5) :=
    ⟨(z.1, z.2 - (k + 1 : ℕ)), ⟨mem_univ _, hr⟩, rfl⟩
  have hyU : y ∈ endReferenceRegion e :=
    endClosedSlab_subset_reference e (by norm_num) (by norm_num) hy
  have htranslation : endAxialTranslation e (k + 1 : ℕ) y = x := by
    rw [show y = e.coordinate (z.1, z.2 - (k + 1 : ℕ)) from rfl,
      endAxialTranslation_coordinate e (k + 1 : ℕ) (by linarith [hr.1])]
    simpa only [sub_add_cancel, Prod.mk.eta] using hcoord
  have hkpos : -3 < ((k + 1 : ℕ) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (k + 1)
    linarith
  have hj := hN k hk T ⟨hT.1.le, le_rfl⟩ y hy
  have hc : (F.flow.connection T).curvatureDerivativeNorm 0 x ≤ K := by
    rw [← htranslation]
    exact hcurvature (F.flow.connection T) (endReferenceRegion_isOpen e)
      (endReferenceTranslation_contMDiffOn e hkpos)
      (fun w hw => endReferenceTranslation_mfderiv_isInvertible e hkpos hw)
      hyU hj.1 hj.2
  rw [LeviCivitaData.curvatureDerivativeNorm_zero] at hc
  calc
    |(F.flow.connection T).scalarCurvature x| ≤
        (3 : ℝ) ^ 2 * (F.flow.connection T).curvatureTensorNorm x :=
      M10.abs_scalarCurvature_le (F.flow.metric T) (F.flow.connection T) x
    _ ≤ 9 * K := by nlinarith

end PoincareConjecture.M34
