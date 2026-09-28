import PoincareConjecture.Proofs.M08.JacobiRepresentative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def jacobiPairResidual {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (S : Set ℝ) (s : ℝ)
    (Y P DP W : TangentSpace (𝓡 n) (α s)) : ℝ :=
  let A := curveVelocityWithin (n := n) α S s
  let D := F.connection (T - s ^ 2)
  (F.metric (T - s ^ 2)).inner (α s) DP W +
    D.curvatureTensor (α s) Y A W A -
    2 * s * backwardConnectionVariationPairing D (α s) A Y W -
    2 * s ^ 2 * D.hessian D.scalarCurvature (α s) Y W +
    4 * s * ricciDerivativePairing D (α s) Y A W +
    4 * s * D.ricci (α s) P W

structure IsJacobiPairOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (α : ℝ → M) (S : Set ℝ) (a b : ℝ)
    (z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : Prop where
  ordered : a < b
  interval_subset : Icc a b ⊆ S
  first_smooth : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
    (fun s ↦ Bundle.TotalSpace.mk' (E := TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n)) (α s) (z s).1) (Icc a b)
  second_smooth : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
    (fun s ↦ Bundle.TotalSpace.mk' (E := TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n)) (α s) (z s).2) (Icc a b)
  equations : ∃ EY : ParametricAlongCurveExtensionOn (Icc a b) α (fun s ↦ (z s).1),
    ∃ EP : ParametricAlongCurveExtensionOn (Icc a b) α (fun s ↦ (z s).2),
      (∀ s ∈ Icc a b, pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
        α (fun r ↦ (z r).1) (Icc a b) EY s = (z s).2) ∧
      ∀ s ∈ Icc a b, ∀ W : TangentSpace (𝓡 n) (α s),
        jacobiPairResidual F T α S s (z s).1 (z s).2
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
            α (fun r ↦ (z r).2) (Icc a b) EP s) W = 0

variable {J : Set ℝ} {F : RicciFlow n M J} {T : ℝ} {α : ℝ → M} {S : Set ℝ}
  {a b : ℝ} {z w : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}

theorem IsJacobiPairOn.congr (h : IsJacobiPairOn F T α S a b z)
    (hzw : EqOn z w (Icc a b)) : IsJacobiPairOn F T α S a b w := by
  obtain ⟨EY, EP, hY, hP⟩ := h.equations
  have hcurve : EqOn α α (Icc a b) := fun _ _ ↦ rfl
  have hfirst : ∀ s ∈ Icc a b, (z s).1 = (w s).1 := fun s hs ↦ congrArg Prod.fst (hzw hs)
  have hsecond : ∀ s ∈ Icc a b, (z s).2 = (w s).2 := fun s hs ↦ congrArg Prod.snd (hzw hs)
  let EY' := transferParametricExtension hcurve hfirst EY
  let EP' := transferParametricExtension hcurve hsecond EP
  refine ⟨h.ordered, h.interval_subset, ?_, ?_, EY', EP', ?_, ?_⟩
  · apply h.first_smooth.congr
    intro s hs
    rw [← hzw hs]
  · apply h.second_smooth.congr
    intro s hs
    rw [← hzw hs]
  · intro s hs
    exact (pullbackCovariantDerivative_transfer F (fun r ↦ T - r ^ 2)
      hcurve hfirst EY hs).symm.trans ((hY s hs).trans (hsecond s hs))
  · intro s hs W
    rw [← pullbackCovariantDerivative_transfer F (fun r ↦ T - r ^ 2)
      hcurve hsecond EP hs, ← hfirst s hs, ← hsecond s hs]
    exact hP s hs W

theorem IsJacobiPairOn.equations_for_extensions (h : IsJacobiPairOn F T α S a b z)
    (hα : ∀ s ∈ Icc a b, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (EY : ParametricAlongCurveExtensionOn (Icc a b) α (fun s ↦ (z s).1))
    (EP : ParametricAlongCurveExtensionOn (Icc a b) α (fun s ↦ (z s).2)) :
    (∀ s ∈ Icc a b, pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
      α (fun r ↦ (z r).1) (Icc a b) EY s = (z s).2) ∧
    ∀ s ∈ Icc a b, ∀ W : TangentSpace (𝓡 n) (α s),
      jacobiPairResidual F T α S s (z s).1 (z s).2
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
          α (fun r ↦ (z r).2) (Icc a b) EP s) W = 0 := by
  obtain ⟨EY₀, EP₀, hY, hP⟩ := h.equations
  constructor
  · intro s hs
    rw [← pullbackCovariantDerivative_extension_independent F (fun r ↦ T - r ^ 2)
      EY₀ EY hs (uniqueDiffOn_Icc h.ordered s hs) (hα s hs)]
    exact hY s hs
  · intro s hs W
    rw [← pullbackCovariantDerivative_extension_independent F (fun r ↦ T - r ^ 2)
      EP₀ EP hs (uniqueDiffOn_Icc h.ordered s hs) (hα s hs)]
    exact hP s hs W

theorem IsJacobiPairOn.restrict (h : IsJacobiPairOn F T α S a b z)
    (hα : ∀ s ∈ Icc a b, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    IsJacobiPairOn F T α S c d z := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  obtain ⟨EY, EP, hY, hP⟩ := h.equations
  let EY' := restrictParametricSectionExtension hsub EY
  let EP' := restrictParametricSectionExtension hsub EP
  refine ⟨hcd, hsub.trans h.interval_subset,
    h.first_smooth.mono hsub, h.second_smooth.mono hsub, EY', EP', ?_, ?_⟩
  · intro s hs
    exact (pullbackCovariantDerivative_restrict F (fun r ↦ T - r ^ 2) hsub EY
      (uniqueDiffOn_Icc h.ordered s (hsub hs)) (uniqueDiffOn_Icc hcd s hs)
      (hα s (hsub hs))).symm.trans (hY s (hsub hs))
  · intro s hs W
    rw [← pullbackCovariantDerivative_restrict F (fun r ↦ T - r ^ 2) hsub EP
      (uniqueDiffOn_Icc h.ordered s (hsub hs)) (uniqueDiffOn_Icc hcd s hs)
      (hα s (hsub hs))]
    exact hP s (hsub hs) W

end PoincareConjecture.M08
