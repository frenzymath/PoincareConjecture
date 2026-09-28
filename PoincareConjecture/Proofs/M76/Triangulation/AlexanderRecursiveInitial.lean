import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSlab
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSingleVertexSlab

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem nonempty_alexanderHalfSlab_of_singleVertex
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    (hq : q ∈ closure ((K.space ∩ {x | A x = 0}) \ {q}))
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z) :
    Nonempty (AlexanderHalfSlab K.space A q β) := by
  classical
  obtain ⟨upper, T, R, J, C, hC, hJ, hJR, hfull, hRzero, hcontact,
      hradial, hcontactRadial, hupperPL, hupper, hqzero, hpos,
      _, hheight, hbottom, hbase⟩ :=
    K.exists_finitePL_singleVertexSlab_with_contacts hK hpure A hqK hAq hq hβ hreg
  exact ⟨{
    width_pos := hβ
    apex_mem := K.vertices_subset_space hqK
    apex_height := hAq
    upper := upper
    collar := T
    residual := R
    residualComplex := J
    chart := C
    chart_finitePL := hC
    residual_finite := hJ
    residual_space := hJR
    cover := hfull
    residual_zero := hRzero
    roof_contact := hcontact
    radialTop := (K.closedStar q).space ∩ {x | A x = β}
    contactTop := (K.link q).space ∩ {x | A x = β}
    residual_radial := hradial
    contact_radial := hcontactRadial
    upper_finitePL := hupperPL
    upper_bounds := hupper
    apex_upper := hqzero
    upper_pos := hpos
    height := hheight
    bottom := hbottom
    bottom_covered := hbase }⟩

end Geometry.SimplicialComplex
