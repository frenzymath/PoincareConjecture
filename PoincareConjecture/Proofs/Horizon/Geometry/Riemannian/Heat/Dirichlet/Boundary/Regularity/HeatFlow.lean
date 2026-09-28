import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Equation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.EnergyFlow
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Regularity.Tangential








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

open Poincare.Analysis.Sobolev

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem heatPower_memWkp_on_precompact
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {U : Set E} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (hone : ∀ z ∈ U, χ (e z) = 1)
    (B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ)
    (hBA : EqOn B.a (divergenceCoefficients g e) U)
    (hBρ : EqOn B.c (g.pullbackVolumeDensity e) U) (r : ℕ) :
    ∀ {V : Set E}, IsOpen V → IsCompact (closure V) → closure V ⊆ U →
      ∀ (k : ℕ) (t : ℝ), 0 < t → ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
        Euclidean.MemWkp r 2
          (chartPullback e (fun y => χ y * toL2 D Ω
            (energyHeatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
              S.isOpen S.isCompact_closure k t f) y))
          (V ∩ {z : E | 0 < z 0}) := by
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  let hn := Nat.pos_of_ne_zero (NeZero.ne n)
  induction r with
  | zero =>
    intro V _ _ _ k t _ f
    apply Euclidean.MemWkp.zero_iff_memLp.mpr
    exact (memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat
      (energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure k t f)).1.1.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)
  | succ r ih =>
    intro V hV hVc hVU k t ht f
    obtain ⟨W, hW, hVW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hVc hU hVU
    have hWU' : W ⊆ U := subset_closure.trans hWU
    let u := energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure k t f
    let v := energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure (k + 1) t f
    have hsol : ∀ w : H1Zero D Ω,
        ⟪u, w⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω w⟫_ℝ = ⟪toL2 D Ω v, toL2 D Ω w⟫_ℝ := by
      intro w
      have hid := energyHeatSpectralPower_pairing D Ω hn S.isOpen S.isCompact_closure k ht f w
      rw [← toDomainL2_energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure k ht f,
        ← toDomainL2_energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure (k + 1) ht f,
        inner_toDomainL2 S.isOpen.measurableSet, inner_toDomainL2 S.isOpen.measurableSet] at hid
      exact hid
    obtain ⟨hu0, heq⟩ := weakSolution_chosen_divergence e he hei χ hχ hc hs hflat
      hW hWc (hWU.trans hUs) (fun z hz => hone z (hWU' hz)) B
      (hBA.mono hWU') (hBρ.mono hWU') u v hsol
    have hWHc : IsCompact (closure (W ∩ H)) :=
      hWc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
    have hf := BoundaryLocalization.memWkp_mul_smooth_of_isCompact_closure r
      (hW.inter hH) hWHc (ih hW hWc hWU (k + 1) t ht f) B.smooth_c
    exact (BoundaryTangential.memWkp_add_two_of_local_weakEquation r B hW hV hVc hVW
      hu0 hf heq).le_succ



theorem exists_local_heatPower_memWkp (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (V : Set E),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ (r k : ℕ) (t : ℝ), 0 < t → ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
        Euclidean.MemWkp r 2
          (chartPullback e (fun y => χ y * toL2 D Ω
            (energyHeatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
              S.isOpen S.isCompact_closure k t f) y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, W, hx, hxW, hW, hWc, hWs, he, hei, hχ, hc, hs, hone, hflat, _⟩ :=
    exists_local_memWkp_two_of_weakSolution D S x
  obtain ⟨U, hU, hxU, hUW, hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  have hUW' : U ⊆ W := subset_closure.trans hUW
  have hUs : closure U ⊆ e.source := hUW.trans (subset_closure.trans hWs)
  obtain ⟨B, hBA, hBρ⟩ := exists_elliptic_form_on_compact (g := g) e he hei hUc hUs
  obtain ⟨V, hV, hxV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hU hxU
  refine ⟨e, χ, V, hx, hxV (mem_singleton _), hV, hVc,
    hVU.trans (subset_closure.trans hUs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hUW' (hVU (subset_closure hz))), hflat, ?_⟩
  intro r
  exact heatPower_memWkp_on_precompact D S e he hei χ hχ hc hs hflat hU
    (subset_closure.trans hUs) (fun z hz => hone z (hUW' hz)) B
    (hBA.mono subset_closure) (hBρ.mono subset_closure) r hV hVc hVU

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
