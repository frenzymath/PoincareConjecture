import PoincareConjecture.Proofs.M14.Sec6_2_SurfaceTorsion
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence
import PoincareConjecture.Proofs.M14.Sec6_2_VariationClock
import PoincareConjecture.Proofs.M14.Sec6_2_OpenFieldExtension

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem exists_variation_velocity_parameter_extension (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    Nonempty (M14PullbackExtension G (fun u => V.squareFamily s u) V.parameterDomain
      (variationSquareVelocity V s)) := by
  have hP : IsOpen V.parameterDomain := by rw [V.parameterDomain_eq]; exact isOpen_Ioo
  apply exists_pullbackExtension_of_isOpen hP
  exact (variationSquareVelocity_smooth V).comp
    ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn (fun _ hu => ⟨hs, hu⟩)

theorem variationSquareVelocity_eq_surfaceHorizontalFst (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (u : ℝ) :
    variationSquareVelocity V s u =
      surfaceHorizontalFst (fun z => V.squareFamily z.1 z.2) s u := by
  unfold variationSquareVelocity surfaceHorizontalFst
  erw [mfderivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]

private theorem horizontal_transport_heq {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : HEq (h.symm ▸ v : G.Horizontal r) v := by
  cases h
  rfl

set_option maxHeartbeats 1000000 in

theorem variation_covariantDerivative_commute
    (hCoordinates : M12MetricPredecessors.{0} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (E : M14PullbackExtension G (fun u => V.squareFamily s u) V.parameterDomain
      (variationSquareVelocity V s)) :
    HEq (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      (M14VariationField V) D.variation_extension s)
      (M14HorizontalCovariantDerivative G (fun u => V.squareFamily s u) V.parameterDomain
        (variationSquareVelocity V s) E 0) := by
  let α : ℝ × ℝ → G.Point := fun z => V.squareFamily z.1 z.2
  have hP : IsOpen V.parameterDomain := by rw [V.parameterDomain_eq]; exact isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hbase : R.curve = fun r => α (r, 0) := (funext V.square_base).symm
  have hfield : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂,
      HEq (M14VariationField V r) (surfaceHorizontalSnd α r 0) := by
    intro r _
    exact horizontal_transport_heq (V.square_base r) _
  have hvelocity : ∀ v ∈ V.parameterDomain,
      HEq (variationSquareVelocity V s v) (surfaceHorizontalFst α s v) := by
    intro v _
    exact heq_of_eq (variationSquareVelocity_eq_surfaceHorizontalFst V hs v)
  let ES := pullbackExtensionCongr D.variation_extension hbase hfield
  let EU := pullbackExtensionCongr E rfl hvelocity
  have hα : ContMDiffOn ((𝓘(ℝ)).prod 𝓘(ℝ)) (spacetimeModel n) ∞ α
      (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ×ˢ V.parameterDomain) :=
    V.square_smooth.mono (fun z hz => V.square_contains ⟨Ioo_subset_Icc_self hz.1, hz.2⟩)
  have hc := horizontalCovariantDerivative_surface_commute hCoordinates
    (isOpen_Ioo.prod hP) hα ⟨hs, hzero⟩ (Icc_mem_nhds hs.1 hs.2) (hP.mem_nhds hzero) ES EU
  exact (horizontalCovariantDerivative_congr D.variation_extension hbase hfield s).trans
    ((heq_of_eq hc).trans (horizontalCovariantDerivative_congr E rfl hvelocity 0).symm)

end PoincareConjecture.M14
