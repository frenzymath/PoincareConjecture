import PoincareConjecture.Proofs.M14.Mathlib.RectanglePartialTangent
import PoincareConjecture.Proofs.M14.Sec6_2_OpenFieldExtension
import PoincareConjecture.Proofs.M14.Sec6_2_SquareRootVelocityExtension

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

private theorem parameterDomain_isOpen (V : M14LVariationData G p R) :
    IsOpen V.parameterDomain := by
  rw [V.parameterDomain_eq]
  exact isOpen_Ioo

private theorem zero_mem_parameterDomain (V : M14LVariationData G p R) :
    (0 : ℝ) ∈ V.parameterDomain := by
  rw [V.parameterDomain_eq]
  exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩

theorem variation_endpoint_field_smooth (V : M14LVariationData G p R) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × ℝ => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (V.squareFamily z.1 z.2)
          (M14EndpointVariationField V z.1 z.2))
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain) := by
  have hI : UniqueDiffOn ℝ (M14SqrtParameterInterval τ₁ τ₂) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hrect := V.square_smooth.mono V.square_contains
  have htan := hrect.contMDiffOn_partialTangent_snd_prod hI (parameterDomain_isOpen V) (1 : ℝ)
      (k := ∞) (by simp)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj
          (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  exact hproj.comp_contMDiffOn htan

theorem variation_field_smooth (V : M14LVariationData G p R) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (R.curve s) (M14VariationField V s))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  have hv := (variation_endpoint_field_smooth V).comp
    (contMDiff_id.prodMk (contMDiff_const (c := (0 : ℝ)))).contMDiffOn
      (fun _ hs => ⟨hs, zero_mem_parameterDomain V⟩)
  apply hv.congr
  intro s _
  apply Bundle.TotalSpace.ext (V.square_base s).symm
  simp only [M14VariationField, M14EndpointVariationField, Function.comp_apply, id_eq]
  have htransport {q r : G.Point} (h : q = r) (v : G.Horizontal q) :
      HEq (h.symm ▸ v : G.Horizontal r) v := by
    cases h
    rfl
  exact htransport (V.square_base s) _

theorem exists_variation_field_extension (V : M14LVariationData G p R) :
    Nonempty (M14PullbackExtension G R.curve
      (M14SqrtParameterInterval τ₁ τ₂) (M14VariationField V)) :=
  exists_pullbackExtension_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
    (variation_field_smooth V)

theorem exists_endpoint_variation_extension (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    Nonempty (M14PullbackExtension G (fun u => V.squareFamily s u)
      V.parameterDomain (M14EndpointVariationField V s)) := by
  apply exists_pullbackExtension_of_isOpen (parameterDomain_isOpen V)
  exact (variation_endpoint_field_smooth V).comp
    ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn
      (fun _ hu => ⟨hs, hu⟩)

theorem exists_variationDerivativeData (V : M14LVariationData G p R) :
    Nonempty (M14VariationDerivativeData V) := by
  classical
  obtain ⟨Ebase⟩ := exists_squareRoot_velocity_extension R
  obtain ⟨Evar⟩ := exists_variation_field_extension V
  exact ⟨{
    base_extension := Ebase
    variation_extension := Evar
    endpoint_extension := fun _ hs => Classical.choice (exists_endpoint_variation_extension V hs)
  }⟩

end PoincareConjecture.M14
