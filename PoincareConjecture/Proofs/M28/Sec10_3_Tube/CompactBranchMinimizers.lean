import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizer

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture

open M28

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M}

private theorem finite_lt_toReal_add_one {l : ℝ≥0∞} (hl : l ≠ ⊤) :
    l < ENNReal.ofReal (l.toReal + 1) := by
  apply (ENNReal.toReal_lt_toReal hl ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  linarith

namespace DoubleCappedTubeCertificate

omit [T2Space M] in

theorem isOpen_carrier (C : DoubleCappedTubeCertificate g) : IsOpen C.carrier := by
  rw [C.carrier_eq_union]
  exact (C.cap₁.carrier_open.union C.tube.carrier_open).union C.cap₂.carrier_open

omit [T2Space M] in

theorem exists_intrinsic_minimizing_sequence (C : DoubleCappedTubeCertificate g)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγC : MapsTo γ (Icc a b) C.carrier)
    (hfinite : g.pathELength γ a b ≠ ⊤) :
    ∃ paths : ℕ → ℝ → M,
      (∀ k, paths k 0 = γ a ∧ paths k 1 = γ b ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (paths k) (Icc (0 : ℝ) 1) ∧
        MapsTo (paths k) (Icc (0 : ℝ) 1) C.carrier ∧
        g.pathELength (paths k) 0 1 <
          ENNReal.ofReal ((g.pathELength γ a b).toReal + 1)) ∧
      Tendsto (fun k => g.pathELength (paths k) 0 1) atTop
        (𝓝 (intrinsicEDist g C.carrier (γ a) (γ b))) := by
  exact exists_intrinsic_minimizing_sequence_of_path g hab hγ hγC
    (finite_lt_toReal_add_one hfinite)

theorem exists_intrinsic_minimizer (C : DoubleCappedTubeCertificate g)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγC : MapsTo γ (Icc a b) C.carrier)
    (hfinite : g.pathELength γ a b ≠ ⊤) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) C.carrier ∧
      g.pathELength σ 0 1 = intrinsicEDist g C.carrier (γ a) (γ b) ∧
      g.pathELength σ 0 1 ≠ ⊤ ∧
      g.pathELength σ 0 1 ≤ g.pathELength γ a b := by
  obtain ⟨paths, hpaths, hlength⟩ :=
    C.exists_intrinsic_minimizing_sequence hab hγ hγC hfinite
  obtain ⟨σ, h0, h1, hσ, hσC, hσlength, hσfinite⟩ :=
    exists_intrinsic_minimizer_of_compact_sequence g
      ⟨C.carrier, C.isOpen_carrier⟩ C.compact (subset_refl C.carrier)
      (fun k => (hpaths k).2.2.1) (fun k => (hpaths k).1)
      (fun k => (hpaths k).2.1) (fun k => (hpaths k).2.2.2.1)
      (fun k => (hpaths k).2.2.2.2) hlength
  refine ⟨σ, h0, h1, hσ, hσC, hσlength, hσfinite, ?_⟩
  rw [hσlength]
  exact intrinsicEDist_le_pathELength g hab hγ hγC

end DoubleCappedTubeCertificate

namespace SphereBundleCircleCertificate

omit [T2Space M] [T3Space M] [MeasurableSpace M] [BorelSpace M] in

theorem isOpen_carrier {X : Set M} (C : SphereBundleCircleCertificate g X) :
    IsOpen C.carrier := by
  rw [C.neck_cover]
  exact isOpen_iUnion (fun N => N.val.carrier_open)

omit [T2Space M] [T3Space M] [MeasurableSpace M] [BorelSpace M] in

theorem exists_intrinsic_minimizing_sequence {X : Set M}
    (C : SphereBundleCircleCertificate g X)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγC : MapsTo γ (Icc a b) C.carrier)
    (hfinite : g.pathELength γ a b ≠ ⊤) :
    ∃ paths : ℕ → ℝ → M,
      (∀ k, paths k 0 = γ a ∧ paths k 1 = γ b ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (paths k) (Icc (0 : ℝ) 1) ∧
        MapsTo (paths k) (Icc (0 : ℝ) 1) C.carrier ∧
        g.pathELength (paths k) 0 1 <
          ENNReal.ofReal ((g.pathELength γ a b).toReal + 1)) ∧
      Tendsto (fun k => g.pathELength (paths k) 0 1) atTop
        (𝓝 (intrinsicEDist g C.carrier (γ a) (γ b))) := by
  exact exists_intrinsic_minimizing_sequence_of_path g hab hγ hγC
    (finite_lt_toReal_add_one hfinite)

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in

theorem exists_intrinsic_minimizer {X : Set M}
    (C : SphereBundleCircleCertificate g X)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγC : MapsTo γ (Icc a b) C.carrier)
    (hfinite : g.pathELength γ a b ≠ ⊤) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) C.carrier ∧
      g.pathELength σ 0 1 = intrinsicEDist g C.carrier (γ a) (γ b) ∧
      g.pathELength σ 0 1 ≠ ⊤ ∧
      g.pathELength σ 0 1 ≤ g.pathELength γ a b := by
  obtain ⟨paths, hpaths, hlength⟩ :=
    C.exists_intrinsic_minimizing_sequence hab hγ hγC hfinite
  obtain ⟨σ, h0, h1, hσ, hσC, hσlength, hσfinite⟩ :=
    exists_intrinsic_minimizer_of_compact_sequence g
      ⟨C.carrier, C.isOpen_carrier⟩ C.compact (subset_refl C.carrier)
      (fun k => (hpaths k).2.2.1) (fun k => (hpaths k).1)
      (fun k => (hpaths k).2.1) (fun k => (hpaths k).2.2.2.1)
      (fun k => (hpaths k).2.2.2.2) hlength
  refine ⟨σ, h0, h1, hσ, hσC, hσlength, hσfinite, ?_⟩
  rw [hσlength]
  exact intrinsicEDist_le_pathELength g hab hγ hγC

end SphereBundleCircleCertificate

end PoincareConjecture
