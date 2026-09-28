import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Level.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.CriticalSet.Closed









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Riemannian.SpaceForm

private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin (1 + 1))) = 1 + 1) :=
  ⟨by simp⟩




theorem exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ p : S2, h p ∈ Icc a b ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0) :
    let D := (roundSphereMetric 2).leviCivitaData
    ∃ U : Opens S2,
      (U : Set S2) = {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}ᶜ ∧
      {p : S2 | p ∈ U ∧ h p ∈ Icc a b} = h ⁻¹' Icc a b ∧
      IsCompact {p : S2 | p ∈ U ∧ h p ∈ Icc a b} ∧
      (∀ c ∈ Icc a b, (U : Set S2) ∩ h ⁻¹' {c} = h ⁻¹' {c}) ∧
      ∃ hreg : ∀ p ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0,
      ∃ (V : Set S2) (δ : Real) (Φ : Real × S2 -> S2),
        IsOpen V ∧ {p : S2 | p ∈ U ∧ h p = a} ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
        ContMDiffOn (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞ Φ
          (Ioo (-δ) (b - a + δ) ×ˢ V) ∧
        (∀ p ∈ V, Φ (0, p) = p) ∧
        (∀ p ∈ V, (∀ t ∈ Ioo (-δ) (b - a + δ), Φ (t, p) ∈ U) ∧
          IsMIntegralCurveOn (I := 𝓡 2) (fun t => Φ (t, p))
            (D.normalizedGradient h) (Ioo (-δ) (b - a + δ))) ∧
        ∀ c ∈ Icc a b,
          letI := openLevelSetChartedSpace hh U hreg 1 a
          letI := openLevelSetChartedSpace hh U hreg 1 c
          ∃ e : Diffeomorph (𝓡 1) (𝓡 1) (openLevelSet h U a) (openLevelSet h U c) ∞,
            ∀ x, openLevelIncl h U c (e x) = Φ (c - a, openLevelIncl h U a x) := by
  let U : Opens S2 :=
    ⟨{p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}ᶜ,
      (Poincare.Geometry.Manifold.isClosed_setOf_mfderiv_eq_zero
        (hh.of_le (by simp))).isOpen_compl⟩
  have hreg : ∀ p ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0 := fun _ hp => hp
  have hband : {p : S2 | p ∈ U ∧ h p ∈ Icc a b} = h ⁻¹' Icc a b := by
    ext p
    constructor
    · exact fun hp => hp.2
    · exact fun hp => ⟨hregular p hp, hp⟩
  have hcompact : IsCompact {p : S2 | p ∈ U ∧ h p ∈ Icc a b} := by
    rw [hband]
    exact (isClosed_Icc.preimage hh.continuous).isCompact
  refine ⟨U, rfl, hband, hcompact, ?_, hreg, ?_⟩
  · intro c hc
    apply inter_eq_right.mpr
    intro p hp
    exact hregular p (show h p ∈ Icc a b by
      have heq : h p = c := hp
      rw [heq]
      exact hc)
  · exact (roundSphereMetric 2).leviCivitaData.exists_level_diffeomorphisms_on_compact_regular_band
      hh U hreg hab hcompact



theorem exists_sphere_height_level_diffeomorphisms_on_regular_band
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ p : S2, h p ∈ Icc a b ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0) :
    let D := (roundSphereMetric 2).leviCivitaData
    ∃ U : Opens S2,
      (U : Set S2) = {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}ᶜ ∧
      {p : S2 | p ∈ U ∧ h p ∈ Icc a b} = h ⁻¹' Icc a b ∧
      IsCompact {p : S2 | p ∈ U ∧ h p ∈ Icc a b} ∧
      (∀ c ∈ Icc a b, (U : Set S2) ∩ h ⁻¹' {c} = h ⁻¹' {c}) ∧
      ∃ hreg : ∀ p ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0,
      ∃ (V : Set S2) (δ : Real) (Φ : Real × S2 -> S2),
        IsOpen V ∧ {p : S2 | p ∈ U ∧ h p = a} ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
        ContMDiffOn (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞ Φ
          (Ioo (-δ) (b - a + δ) ×ˢ V) ∧
        (∀ p ∈ V, Φ (0, p) = p) ∧
        (∀ p ∈ V, (∀ t ∈ Ioo (-δ) (b - a + δ), Φ (t, p) ∈ U) ∧
          IsMIntegralCurveOn (I := 𝓡 2) (fun t => Φ (t, p))
            (D.normalizedGradient h) (Ioo (-δ) (b - a + δ))) ∧
        ∀ c ∈ Icc a b,
          letI := openLevelSetChartedSpace hh U hreg 1 a
          letI := openLevelSetChartedSpace hh U hreg 1 c
          ∃ e : Diffeomorph (𝓡 1) (𝓡 1) (openLevelSet h U a) (openLevelSet h U c) ∞,
            ∀ x, openLevelIncl h U c (e x) = Φ (c - a, openLevelIncl h U a x) :=
  (fun _ => exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth
    hh hab hregular) hfinite

end Poincare.Manifold.Schoenflies
