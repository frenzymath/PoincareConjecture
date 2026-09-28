import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronNeighborhoodRetraction
import PoincareConjecture.Proofs.M76.Mathlib.RelativeFinitePLApproximation
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_relative_finitePL_map_to_polyhedron
    (K : SimplicialComplex ℝ E) (J : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hJ : J.faces.Finite)
    {f : E → F} (hf : ContinuousOn f K.space) (hfJ : MapsTo f K.space J.space)
    {S : Set E} (hSK : S ⊆ K.space) (hfS : FinitePiecewiseAffineOn f S) :
    ∃ g : E → F, FinitePiecewiseAffineOn g K.space ∧ EqOn g f S ∧
      MapsTo g K.space J.space ∧
      ∃ H : C(I × K.space, F), (∀ z, H z ∈ J.space) ∧
        (∀ x : K.space, H (0, x) = f x) ∧
        (∀ x : K.space, H (1, x) = g x) ∧
        ∀ (t : I) (x : K.space), (x : E) ∈ S → H (t, x) = f x := by
  obtain ⟨N, r, hN, hJN, _, hr, hrJ, hrfix⟩ :=
    J.exists_finitePL_neighborhood_retraction hJ isOpen_univ (subset_univ _)
  obtain ⟨a, ha, haS, hsegment⟩ := K.exists_relative_finitePL_approximation_in_open
    hK hf hSK hfS isOpen_interior (fun _ hx => hJN (hfJ hx))
  have haN : MapsTo a K.space N.space := fun x hx =>
    interior_subset (hsegment x hx (right_mem_segment ℝ (f x) (a x)))
  let g := r ∘ a
  have hg : FinitePiecewiseAffineOn g K.space :=
    (hr.finitePiecewiseAffineOn hN).comp ha haN
  have hgS : EqOn g f S := by
    intro x hx
    change r (a x) = f x
    rw [haS hx]
    exact hrfix (hfJ (hSK hx))
  let B : I × K.space → F := fun z =>
    (1 - (z.1 : ℝ)) • f z.2 + (z.1 : ℝ) • a z.2
  have ht : Continuous (fun z : I × K.space => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hfc : Continuous (fun z : I × K.space => f z.2) :=
    (hf.comp_continuous continuous_subtype_val (fun x => x.property)).comp continuous_snd
  have hac : Continuous (fun z : I × K.space => a z.2) :=
    (ha.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property)).comp
      continuous_snd
  have hB : Continuous B := ((continuous_const.sub ht).smul hfc).add (ht.smul hac)
  have hBN (z : I × K.space) : B z ∈ N.space := by
    apply interior_subset
    apply hsegment z.2 z.2.property
    exact ⟨1 - (z.1 : ℝ), (z.1 : ℝ), sub_nonneg.mpr z.1.property.2,
      z.1.property.1, sub_add_cancel 1 (z.1 : ℝ), rfl⟩
  let H : C(I × K.space, F) :=
    ⟨r ∘ B, (hr.continuousOn hN).comp_continuous hB hBN⟩
  refine ⟨g, hg, hgS, hrJ.comp haN, H, fun z => hrJ (hBN z), ?_, ?_, ?_⟩
  · intro x
    change r ((1 - (0 : ℝ)) • f x + 0 • a x) = f x
    simpa only [sub_zero, one_smul, zero_smul, add_zero, id_eq] using hrfix (hfJ x.property)
  · intro x
    change r ((1 - (1 : ℝ)) • f x + 1 • a x) = r (a x)
    simp only [sub_self, zero_smul, one_smul, zero_add]
  · intro t x hx
    change r ((1 - (t : ℝ)) • f x + (t : ℝ) • a x) = f x
    rw [haS hx, ← add_smul, sub_add_cancel, one_smul]
    exact hrfix (hfJ x.property)

end Geometry.SimplicialComplex
