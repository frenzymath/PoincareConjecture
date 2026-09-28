import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerLipschitzClass
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCompetitors

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}

private theorem m65NormalizedWeak_energy_competitor
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (compact : IsCompact (univ : Set M)) {γ : C1FreeLoopSpace (M := M)}
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D : LipschitzSpanningDisk g γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : M65WeakDisk e γ, F.Normalized a b c ∧ F.energy g ≤ D.area + ε := by
  obtain ⟨D', _harea, _hi, henergy, ha, hb, hc⟩ :=
    m65SpanningDisk_exists_normalized_energy_competitor a b c hab hac hbc D ε hε
  obtain ⟨F, _hvalue, hparameter, hE⟩ := m65SpanningDisk_weak_member g e he hinj compact D'
  refine ⟨F, ?_, hE.le.trans henergy⟩
  let p : LoopCircle := ⟨orthonormalBasisOneI.repr 1, by simp⟩
  let n : LoopCircle := ⟨orthonormalBasisOneI.repr (-1), by simp⟩
  let ip : LoopCircle := ⟨orthonormalBasisOneI.repr I, by simp⟩
  let im : LoopCircle := ⟨orthonormalBasisOneI.repr (-I), by simp⟩
  have hp : D'.reparameterization.inverse a = p := Subtype.ext ha
  have hn : D'.reparameterization.inverse b = n := Subtype.ext hb
  change F.parameter p = a ∧ F.parameter n = b ∧
    (F.parameter ip = c ∨ F.parameter im = c)
  rw [hparameter]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hp, ContinuousMap.coe_mk] using D'.reparameterization.right_inverse a
  · simpa only [hn, ContinuousMap.coe_mk] using D'.reparameterization.right_inverse b
  · rcases hc with hc | hc
    · have hi : D'.reparameterization.inverse c = ip := Subtype.ext hc
      exact Or.inl (by
        simpa only [hi, ContinuousMap.coe_mk] using D'.reparameterization.right_inverse c)
    · have hi : D'.reparameterization.inverse c = im := Subtype.ext hc
      exact Or.inr (by
        simpa only [hi, ContinuousMap.coe_mk] using D'.reparameterization.right_inverse c)

theorem m65Plateau_weak_minimum (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (γ : C1FreeLoopSpace (M := M)) (hγ : Function.Injective γ)
    (hfill : Nonempty (LipschitzSpanningDisk g γ))
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ F : M65WeakDisk e γ, F.MinimizesNormalizedEnergy g a b c ∧
      F.energy g ≤ fillingArea g γ := by
  obtain ⟨D0⟩ := hfill
  obtain ⟨F0, hF0, _hE0⟩ := m65NormalizedWeak_energy_competitor g e he hinj compact
    a b c hab hac hbc D0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨F, hF⟩ := m65WeakDisk_exists_normalized_minimum g he hinj hemb compact
    γ.continuous (hemb.injective.comp hγ) hab hac hbc F0 hF0
  refine ⟨F, hF, ?_⟩
  have hbound (D : LipschitzSpanningDisk g γ) : F.energy g ≤ D.area := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨Q, hQ, hQE⟩ := m65NormalizedWeak_energy_competitor g e he hinj compact
      a b c hab hac hbc D hε
    exact (hF.2 Q hQ).trans hQE
  apply le_csInf (show (range fun D : LipschitzSpanningDisk g γ => D.area).Nonempty from
    ⟨D0.area, D0, rfl⟩)
  rintro x ⟨D, rfl⟩
  exact hbound D

end PoincareConjecture
