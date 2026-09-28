import PoincareConjecture.Proofs.M09.VariationRegularField
import PoincareConjecture.Proofs.M09.SmoothPartials

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T a b : ℝ} {p : BackwardTimePath F T a b}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareVariationField_chart_smooth (V : LVariation F T a b p) (x0 : M) :
    let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
    let Ω := V.squareDomain ∩ H ⁻¹' (chartAt E x0).source
    let U := (fun r : ℝ ↦ (r, (0 : ℝ))) ⁻¹' Ω
    let v : ℝ → E := fun r ↦ deriv (fun u ↦ (chartAt E x0) (V.squareFamily r u)) 0
    IsOpen U ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U ∧
      (∀ r ∈ U, V.baseSquareCurve r ∈ (chartAt E x0).source) ∧
      ContDiffOn ℝ ∞ v U ∧
      ∀ r ∈ U, chartVectorField x0 (v r) (V.baseSquareCurve r) = squareVariationField V r := by
  let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  let Ω := V.squareDomain ∩ H ⁻¹' (chartAt E x0).source
  let U := (fun r : ℝ ↦ (r, (0 : ℝ))) ⁻¹' Ω
  let f : ℝ × ℝ → E := fun z ↦ (chartAt E x0) (H z)
  let v : ℝ → E := fun r ↦ deriv (fun u ↦ f (r, u)) 0
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hΩ : IsOpen Ω := hH.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt E x0).open_source
  have hf : ContDiffOn ℝ ∞ f Ω :=
    (contMDiffOn_chart.comp (hH.mono Set.inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  have hi : ContDiff ℝ ∞ (fun r : ℝ ↦ (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hbase : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    hH.comp hi.contMDiff.contMDiffOn (fun r hr ↦ hr.1)
  have hv : ContDiffOn ℝ ∞ v U :=
    (contDiffOn_slice_deriv_snd f Ω hΩ hf).comp hi.contDiffOn (fun r hr ↦ hr)
  refine ⟨hΩ.preimage hi.continuous, hbase, fun r hr ↦ hr.2, hv, ?_⟩
  intro r hr
  have hsmooth : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (V.squareFamily r) 0 :=
    (hH.contMDiffAt (V.square_open.mem_nhds hr.1)).comp 0
      ((contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt)
  have hd : HasDerivAt (fun u ↦ (chartAt E x0) (V.squareFamily r u)) (v r) 0 :=
    (hasDerivAt_slice_snd f r 0
      ((hf.contDiffAt (hΩ.mem_nhds hr)).differentiableAt (by simp))).differentiableAt.hasDerivAt
  exact chartVectorField_coordinate_velocity x0 (V.squareFamily r) 0 (v r) hr.2
    (hsmooth.mdifferentiableAt (by simp)) hd

end PoincareConjecture.Proofs.M09
