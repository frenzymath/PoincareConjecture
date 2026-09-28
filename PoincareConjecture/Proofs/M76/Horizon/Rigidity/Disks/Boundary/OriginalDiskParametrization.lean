import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalFiniteCollarModel
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.ExactDiskParametrization









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OriginalFiniteCollarModel.exists_exact_original_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (M : OriginalFiniteCollarModel e R)
    {D S : Set (M.vertices → ℝ × V3)} (hD : IsFinitePLBallPair V2 D S)
    (hDK : D ⊆ M.complex.space) (hfront : D ∩ M.boundary.space = S)
    (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL)
    (r : V2 → X) (hrR : MapsTo r Q2 R)
    (hvalues : ∀ x : Q2, (gamma x : M.vertices → ℝ × V3) = M.coordinates (r x)) :
    ∃ j : V2 → X, PolyhedralPLInCharts e j D2 ∧
      Topology.IsEmbedding (fun x : D2 => j x) ∧ MapsTo j D2 R ∧
      (∀ x : D2, j x ∈ frontier R ↔ (x : V2) ∈ Q2) ∧
      ∀ x ∈ Q2, j x = r x := by
  classical
  obtain ⟨b, hb, hbval, hboundary⟩ :=
    isFinitePLBallPair_unit_cube.exists_extension hD gamma hgamma
  obtain ⟨f, hf, hfb⟩ := hb
  have hfK : MapsTo f D2 M.complex.space := by
    intro x hx
    rw [← hfb ⟨x, hx⟩]
    exact hDK (b ⟨x, hx⟩).property
  let j : V2 → X := fun x => M.inverse (f x)
  have hjval (x : D2) : j x = (M.homeomorph.symm ⟨(b x : M.vertices → ℝ × V3),
      hDK (b x).property⟩ : X) := by
    change (M.inverse (f x) : X) = _
    rw [← hfb x]
    exact M.inverse_eq ⟨(b x : M.vertices → ℝ × V3), hDK (b x).property⟩
  have hjcont : Continuous (fun x : D2 => j x) := by
    apply Continuous.congr _ (fun x => (hjval x).symm)
    exact continuous_subtype_val.comp (M.homeomorph.symm.continuous.comp
      ((continuous_subtype_val.comp b.continuous).subtype_mk _))
  have hjinj : Function.Injective (fun x : D2 => j x) := by
    intro x y hxy
    change j x = j y at hxy
    rw [hjval x, hjval y] at hxy
    have heq := M.homeomorph.symm.injective (Subtype.ext hxy)
    exact b.injective (Subtype.ext (congrArg
      (fun z : M.complex.space => (z : M.vertices → ℝ × V3)) heq))
  have hf' := hf
  obtain ⟨K, hK, hKs, _⟩ := hf'
  have hjPL : PolyhedralPLInCharts e j D2 := by
    have h := M.inverse_pl.comp_finitePiecewiseAffineOn K hK
      (hKs.symm ▸ hf) (hKs.symm ▸ hfK)
    exact hKs ▸ h
  refine ⟨j, hjPL, (hjcont.isClosedEmbedding hjinj).isEmbedding,
    fun x _ => (M.inverse (f x)).property, ?_, ?_⟩
  · intro x
    rw [show j x = (M.inverse (f x) : X) from rfl, M.boundary_eq _ (hfK x.property),
      ← hfb x]
    have hmem : (b x : M.vertices → ℝ × V3) ∈ M.boundary.space ↔
        (b x : M.vertices → ℝ × V3) ∈ S := by
      rw [← hfront]
      exact ⟨fun h => ⟨(b x).property, h⟩, fun h => h.2⟩
    exact hmem.trans (hboundary x).symm
  · intro x hx
    have hv := congrArg Subtype.val (hbval ⟨x, hx⟩)
    change (b ⟨x, sphere_subset_closedBall hx⟩ : M.vertices → ℝ × V3) =
      (gamma ⟨x, hx⟩ : M.vertices → ℝ × V3) at hv
    change (M.inverse (f x) : X) = r x
    rw [← hfb ⟨x, sphere_subset_closedBall hx⟩, hv, hvalues ⟨x, hx⟩]
    exact M.inverse_coordinates _ (hrR hx)

end PoincareConjecture.M76
