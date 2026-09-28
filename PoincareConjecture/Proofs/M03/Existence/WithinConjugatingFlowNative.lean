import PoincareConjecture.Proofs.M03.Existence.TangentHalfSpaceExtensionNative
import PoincareConjecture.Proofs.M03.Existence.FiniteOrderConjugatingFlowNative








set_option autoImplicit false

open Set Manifold
open scoped Topology ContDiff Bundle

noncomputable section

namespace PoincareConjecture.WithinConjugatingFlowNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n
local notation "J" => ModelWithCorners.prod 𝓘(ℝ, ℝ) (𝓡 n)

theorem exists_diffeomorph_family
    (X : ℝ → (x : M) → TangentSpace I x) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hX : ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Ico 0 T₀ ×ˢ univ)) :
    ∃ T > 0, T ≤ T₀ / 2 ∧ ∃ Phi : ℝ → Diffeomorph I I M M ∞,
      Phi 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiffOn J I ∞ (fun q : ℝ × M => Phi q.1 q.2) (Ico 0 T ×ˢ univ) ∧
      ∀ t ∈ Ico 0 T, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Phi s x) (Ico 0 T) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Phi t x))) := by
  apply FiniteOrderConjugatingFlowNative.exists_diffeomorph_family_of_finite_extensions
    (fun q : M × ℝ => X q.2 q.1) (half_pos hT₀)
  intro k
  obtain ⟨Y, hY, hEq⟩ := TangentHalfSpaceExtensionNative.exists_contMDiff_extension_swapped
    (k + 1) X hT₀ (hX.of_le (by
      simpa only [Nat.cast_succ] using
        ENat.natCast_le_of_coe_top_le_withTop (N := ∞) le_rfl (k + 1)))
  exact ⟨Y, hY, fun q hq => hEq q.2 ⟨hq.1, hq.2.le⟩ q.1⟩

theorem exists_neg_intrinsicDeTurck_family
    {g : ℝ → RiemannianMetric n M} {background : RiemannianMetric n M}
    (D : ∀ t : ℝ, LeviCivitaData (g t)) (B : LeviCivitaData background)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hW : ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2
          (DeTurckNative.intrinsicDeTurckField (D q.1) B q.2) : TangentBundle I M))
      (Ico 0 T₀ ×ˢ univ)) :
    ∃ T > 0, T ≤ T₀ / 2 ∧ ∃ Phi : ℝ → Diffeomorph I I M M ∞,
      Phi 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiffOn J I ∞ (fun q : ℝ × M => Phi q.1 q.2) (Ico 0 T ×ˢ univ) ∧
      ∀ t ∈ Ico 0 T, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Phi s x) (Ico 0 T) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(DeTurckNative.intrinsicDeTurckField (D t) B (Phi t x)))) := by
  have hneg : ContMDiffOn J (ModelWithCorners.prod I 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2
          (-(DeTurckNative.intrinsicDeTurckField (D q.1) B q.2)) : TangentBundle I M))
      (Ico 0 T₀ ×ˢ univ) := by
    intro q hq
    exact TimeDependentConjugatingFlowNative.contMDiffWithinAt_neg_intrinsicDeTurckField
      D B (hW q hq)
  exact exists_diffeomorph_family
    (fun t x => -(DeTurckNative.intrinsicDeTurckField (D t) B x)) hT₀ hneg

end PoincareConjecture.WithinConjugatingFlowNative

end
