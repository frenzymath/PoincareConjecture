import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Energy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChartSupport

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

def coordinateExtension
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) : M → ℝ :=
  e.target.indicator (φ ∘ e.symm)

theorem coordinateExtension_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) {y : M} (hy : y ∈ e.target) :
    coordinateExtension e φ y = φ (e.symm y) := indicator_of_mem hy _

theorem coordinateExtension_comp_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    coordinateExtension e φ (e x) = φ x := by
  rw [coordinateExtension_apply e φ (e.map_source hx), e.left_inv hx]

theorem coordinateExtension_eventuallyEq
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) {y : M} (hy : y ∈ e.target) :
    coordinateExtension e φ =ᶠ[𝓝 y] φ ∘ e.symm := by
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact coordinateExtension_apply e φ hz

variable [T2Space M]

theorem tsupport_coordinateExtension_subset_image
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ e.source) :
    tsupport (coordinateExtension e φ) ⊆ e '' tsupport φ := by
  have hK : IsCompact (e '' tsupport φ) :=
    hφc.isCompact.image_of_continuousOn (e.continuousOn.mono hφs)
  apply closure_minimal _ hK.isClosed
  intro y hy
  have hyt : y ∈ e.target := by
    by_contra h
    exact hy (indicator_of_notMem h _)
  refine ⟨e.symm y, subset_tsupport φ ?_, e.right_inv hyt⟩
  simpa only [Function.mem_support, coordinateExtension_apply e φ hyt] using hy

theorem hasCompactSupport_coordinateExtension
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ e.source) : HasCompactSupport (coordinateExtension e φ) :=
  (hφc.isCompact.image_of_continuousOn (e.continuousOn.mono hφs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_coordinateExtension_subset_image e hφc hφs)

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

omit [IsManifold (𝓡 n) ∞ M] in

theorem contMDiff_coordinateExtension
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ e.source) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (coordinateExtension e φ) := by
  apply contMDiff_of_tsupport
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_coordinateExtension_subset_image e hφc hφs hy
  have hyt := e.map_source (hφs hx)
  apply ContMDiffAt.congr_of_eventuallyEq _ (coordinateExtension_eventuallyEq e φ hyt)
  exact hφ.contMDiff.contMDiffAt.comp (e x) (hei.contMDiffAt (e.open_target.mem_nhds hyt))

def EnergyTest.ofCoordinates
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω) :
    EnergyTest D Ω :=
  ⟨coordinateExtension e φ, contMDiff_coordinateExtension e hei hφ hφc
    (hφs.trans inter_subset_left), hasCompactSupport_coordinateExtension e hφc
    (hφs.trans inter_subset_left), by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := tsupport_coordinateExtension_subset_image e hφc
        (hφs.trans inter_subset_left) hy
      exact (hφs hx).2⟩

theorem EnergyTest.ofCoordinates_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    EnergyTest.ofCoordinates (D := D) e hei φ hφ hφc hφs (e x) = φ x :=
  coordinateExtension_comp_apply e φ hx

theorem EnergyTest.chartPullback_ofCoordinates
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω) :
    chartPullback e (EnergyTest.ofCoordinates (D := D) e hei φ hφ hφc hφs) = φ := by
  funext x
  by_cases hx : x ∈ e.source
  · rw [chartPullback_apply e _ hx, EnergyTest.ofCoordinates_apply e hei φ hφ hφc hφs hx]
  · have hxφ : x ∉ tsupport φ := fun h => hx (hφs h).1
    simp [chartPullback, hx, image_eq_zero_of_notMem_tsupport hxφ]

theorem EnergyTest.ofCoordinates_comp_eventuallyEq
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    (fun y => EnergyTest.ofCoordinates (D := D) e hei φ hφ hφc hφs (e y)) =ᶠ[𝓝 x] φ := by
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  exact EnergyTest.ofCoordinates_apply e hei φ hφ hφc hφs hy

end PoincareConjecture.LeviCivitaData.Dirichlet
