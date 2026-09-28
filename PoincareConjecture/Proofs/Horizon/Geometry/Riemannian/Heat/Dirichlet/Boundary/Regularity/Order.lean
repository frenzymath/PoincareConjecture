import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Initial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ClassicalEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Maximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}
  (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

theorem contMDiffOn_heat_test_extension (φ : EnergyTest D Ω) (F : ℝ → (M →ᵇ ℝ))
    (hpos : ∀ t : ℝ, 0 < t → F t =
      heatPowerContinuousTime D S 0 t (toDomainL2 D Ω (φ : H1Zero D Ω)))
    (t : ℝ) (ht : 0 < t) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F t : M → ℝ) Ω := by
  rw [hpos t ht, heatPowerContinuousTime_of_pos D S 0 ht]
  exact contMDiffOn_heatPowerContinuous D S 0 t ht _

theorem hasDerivAt_heat_test_extension (φ : EnergyTest D Ω) (F : ℝ → (M →ᵇ ℝ))
    (hpos : ∀ t : ℝ, 0 < t → F t =
      heatPowerContinuousTime D S 0 t (toDomainL2 D Ω (φ : H1Zero D Ω)))
    (t : ℝ) (ht : 0 < t) (x : M) (hx : x ∈ Ω) :
    HasDerivAt (fun s : ℝ => F s x) (D.laplacian (F t : M → ℝ) x) t := by
  let f := toDomainL2 D Ω (φ : H1Zero D Ω)
  have hT := hasDerivAt_heatPowerContinuousTime D S 0 ht
  have hd : HasDerivAt (fun s : ℝ => heatPowerContinuousTime D S 0 s f x)
      (-heatPowerContinuousTime D S 1 t f x) t := by
    have h := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t
      (hT.clm_apply (hasDerivAt_const t f))
    convert! h using 1
    simp
  have heq : (fun s : ℝ => F s x) =ᶠ[𝓝 t]
      fun s => heatPowerContinuousTime D S 0 s f x := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [hpos s hs]
  have hLap : D.laplacian (F t : M → ℝ) x =
      -heatPowerContinuousTime D S 1 t f x := by
    rw [hpos t ht, heatPowerContinuousTime_of_pos D S 0 ht,
      heatPowerContinuousTime_of_pos D S 1 ht]
    exact heatPowerContinuous_laplacian D S 0 t ht f x hx
  rw [hLap]
  exact hd.congr_of_eventuallyEq heq

theorem heatPowerContinuous_test_le (φ : EnergyTest D Ω) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ x : M, φ x ≤ C) (t : ℝ) (ht : 0 < t) (x : M) :
    heatPowerContinuous D S 0 t ht (toDomainL2 D Ω (φ : H1Zero D Ω)) x ≤ C := by
  obtain ⟨F, hF, hinit, hpos⟩ := exists_continuous_heat_test D S φ
  have hFc : Continuous (fun p : M × ℝ => F p.2 p.1) :=
    continuous_eval.comp ((hF.comp continuous_snd).prodMk continuous_fst)
  have hzero (y : M) (hy : y ∉ Ω) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : F s y = 0 := by
    by_cases hsp : 0 < s
    · rw [hpos s hsp, heatPowerContinuousTime_of_pos D S 0 hsp,
        heatPowerContinuous_zero_outside D S 0 s hsp _ y hy]
    · have hs0 : s = 0 := le_antisymm (not_lt.mp hsp) hs.1
      rw [hs0, hinit]
      exact image_eq_zero_of_notMem_tsupport (fun h => hy (φ.support_subset h))
  have hle := le_of_subsolution_supersolution D S.isOpen S.isCompact_closure
    (F := fun y s => F s y) (G := fun _ _ => C)
    (F' := fun y s => D.laplacian (F s : M → ℝ) y) (G' := fun _ _ => 0)
    (a := 0) (b := t) hFc.continuousOn continuousOn_const
    (fun s hs => contMDiffOn_heat_test_extension D S φ F hpos s hs.1)
    (fun _ _ => contMDiff_const.contMDiffOn)
    (fun y hy s hs => (hasDerivAt_heat_test_extension D S φ F hpos s hs.1 y hy).hasDerivWithinAt)
    (fun _ _ s _ => (hasDerivAt_const s C).hasDerivWithinAt)
    (fun _ _ _ _ => le_rfl)
    (fun y _ _ _ => D.laplacian_nonpos_of_isLocalMax contMDiff_const
      (Eventually.of_forall fun _ => le_rfl))
    (fun y _ hy s hs => by rw [hzero y hy s hs]; exact hC)
    (fun y _ => by rw [hinit]; exact hφ y)
  by_cases hx : x ∈ Ω
  · have h := hle x (subset_closure hx) t ⟨ht.le, le_rfl⟩
    rw [hpos t ht, heatPowerContinuousTime_of_pos D S 0 ht] at h
    exact h
  · rw [heatPowerContinuous_zero_outside D S 0 t ht _ x hx]
    exact hC

theorem heatPowerContinuous_test_nonneg (φ : EnergyTest D Ω)
    (hφ : ∀ x : M, 0 ≤ φ x) (t : ℝ) (ht : 0 < t) (x : M) :
    0 ≤ heatPowerContinuous D S 0 t ht (toDomainL2 D Ω (φ : H1Zero D Ω)) x := by
  have h := heatPowerContinuous_test_le D S (-φ) 0 le_rfl
    (fun y => neg_nonpos.mpr (hφ y)) t ht x
  simpa only [UniformSpace.Completion.coe_neg, map_neg,
    BoundedContinuousFunction.neg_apply, neg_nonpos] using h

theorem heatPowerContinuous_test_mem_Icc (φ : EnergyTest D Ω) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ x : M, φ x ∈ Icc 0 C) (t : ℝ) (ht : 0 < t) (x : M) :
    heatPowerContinuous D S 0 t ht (toDomainL2 D Ω (φ : H1Zero D Ω)) x ∈ Icc 0 C :=
  ⟨heatPowerContinuous_test_nonneg D S φ (fun y => (hφ y).1) t ht x,
    heatPowerContinuous_test_le D S φ C hC (fun y => (hφ y).2) t ht x⟩

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
