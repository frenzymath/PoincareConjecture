import PoincareConjecture.Statements.M63RampEstimates

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

section Curves

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def m63RestrictFlow {J : Set ℝ} (F : RicciFlow n M J) (J' : Set ℝ)
    (hsub : J' ⊆ J) (hOrd : J'.OrdConnected) (hNontriv : J'.Nontrivial) :
    RicciFlow n M J' where
  metric := F.metric
  connection := F.connection
  interval := hOrd
  nontrivial := hNontriv
  smooth := F.smooth.mono (Set.prod_mono hsub Set.Subset.rfl)
  equation t ht x v w := (F.equation t (hsub ht) x v w).mono hsub

def m63RestrictClosedFlow {J : Set ℝ} (F : RicciFlow n M J) (s t : ℝ)
    (hsub : Set.Icc s t ⊆ J) (hst : s < t) : RicciFlow n M (Set.Icc s t) :=
  m63RestrictFlow F (Set.Icc s t) hsub Set.ordConnected_Icc
    ⟨s, ⟨le_rfl, hst.le⟩, t, ⟨hst.le, le_rfl⟩, hst.ne⟩

variable {a b : ℝ}

def m63RestrictCircleProduct {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (s t : ℝ) (hsub : Set.Icc s t ⊆ Set.Icc a b) (hst : s < t) :
    M62.CircleProductData (m63RestrictClosedFlow F s t hsub hst) circumference where
  circle := P.circle
  charts := P.charts
  flow := m63RestrictClosedFlow P.flow s t hsub hst
  metric_eq := P.metric_eq

theorem m63C2_of_m62 {F : RicciFlow n M (Set.Icc a b)} {c : ℝ → ℝ → M}
    (h : M62ShrinkingCurve F c) : M63C2ShrinkingCurveOn F c (Set.Icc a b) where
  domain_subset := Set.Subset.rfl
  periodic := h.periodic
  spatial_regular := h.spatial_regular
  joint_c1 := by
    simpa only [interior_Icc] using h.joint_smooth.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  immersed := h.immersed
  continuous := h.continuous
  velocity_continuous := h.velocity_continuous
  curvature_continuous := h.curvature_continuous
  equation := by simpa only [interior_Icc] using h.equation

theorem m63SmoothClosed_iff_m62 {F : RicciFlow n M (Set.Icc a b)} {c : ℝ → ℝ → M} :
    M63SmoothShrinkingCurveOn F c (Set.Icc a b) ↔ M62ShrinkingCurve F c := by
  constructor
  · intro h
    exact {
      periodic := h.1.periodic
      spatial_regular := h.1.spatial_regular
      joint_smooth := by simpa only [interior_Icc] using h.2
      immersed := h.1.immersed
      continuous := h.1.continuous
      velocity_continuous := h.1.velocity_continuous
      curvature_continuous := h.1.curvature_continuous
      equation := by simpa only [interior_Icc] using h.1.equation }
  · intro h
    exact ⟨m63C2_of_m62 h, by simpa only [interior_Icc] using h.joint_smooth⟩

theorem m63SmoothRestriction {F : RicciFlow n M (Set.Icc a b)}
    {c : ℝ → ℝ → M} {J : Set ℝ} (h : M63SmoothShrinkingCurveOn F c J)
    (s t : ℝ) (hJ : Set.Icc s t ⊆ J) (hst : s < t) :
    M62ShrinkingCurve (m63RestrictClosedFlow F s t (hJ.trans h.1.domain_subset) hst) c := by
  have hi : Set.Ioo s t ⊆ interior J := by
    simpa only [interior_Icc] using interior_mono hJ
  exact {
    periodic := fun r hr => h.1.periodic r (hJ hr)
    spatial_regular := fun r hr => h.1.spatial_regular r (hJ hr)
    joint_smooth := h.2.mono (Set.prod_mono Set.Subset.rfl hi)
    immersed := fun r hr => h.1.immersed r (hJ hr)
    continuous := h.1.continuous.mono (Set.prod_mono Set.Subset.rfl hJ)
    velocity_continuous := h.1.velocity_continuous.mono (Set.prod_mono Set.Subset.rfl hJ)
    curvature_continuous := h.1.curvature_continuous.mono (Set.prod_mono Set.Subset.rfl hJ)
    equation := fun r hr => h.1.equation r (hi hr) }

theorem m63RestrictAmbientBounds {F : RicciFlow n M (Set.Icc a b)} {K0 K1 K2 : ℝ}
    (h : CurveEvolutionAmbientBounds F K0 K1 K2) (s t : ℝ)
    (hsub : Set.Icc s t ⊆ Set.Icc a b) (hst : s < t) :
    CurveEvolutionAmbientBounds (m63RestrictClosedFlow F s t hsub hst) K0 K1 K2 where
  riemann r hr := h.riemann r (hsub hr)
  ricci_derivative r hr := h.ricci_derivative r (hsub hr)
  ricci r hr := h.ricci r (hsub hr)

theorem m63M62RestrictedEstimates [T2Space M] [SecondCountableTopology M]
    (hM62 : M62CurveEvolutionTheory.{u}) {F : RicciFlow n M (Set.Icc a b)}
    (hcompact : IsCompact (Set.univ : Set M)) {K0 K1 K2 : ℝ}
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {c : ℝ → ℝ → M} {J : Set ℝ} (hc : M63SmoothShrinkingCurveOn F c J)
    (s t : ℝ) (hJ : Set.Icc s t ⊆ J) (hst : s < t) :
    M62CurveEstimates
      (m63RestrictClosedFlow F s t (hJ.trans hc.1.domain_subset) hst) c K0 K1 K2 := by
  obtain ⟨E⟩ := hM62 n M s t
    (m63RestrictClosedFlow F s t (hJ.trans hc.1.domain_subset) hst) hcompact
  exact (E.curve_theory.estimates K0 K1 K2 hK0 hK1 hK2
    (m63RestrictAmbientBounds hBounds s t (hJ.trans hc.1.domain_subset) hst)
    c (m63SmoothRestriction hc s t hJ hst)).1

end Curves

section Labels

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m63Represents_of_homotopic {q : M59SphereQuotient} {x : M}
    {alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    {Gamma Delta : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    (h : Gamma.Homotopic Delta) (hGamma : M61Represents q x alpha Gamma) :
    M61Represents q x alpha Delta := by
  obtain ⟨seed, normalized, same_class, hseed⟩ := hGamma
  exact ⟨seed, normalized, same_class, h.symm.trans hseed⟩

end Labels

end PoincareConjecture
