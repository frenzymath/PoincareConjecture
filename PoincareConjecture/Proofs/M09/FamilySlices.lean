import PoincareConjecture.Definitions.Ch06.ReducedLength
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_squareSlice_contMDiffAt (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (s : ℝ) (hs : s ∈ Set.Ico 0 (Real.sqrt τmax)) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) s := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.squareFamily z.1 z.2) A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hi : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E × ℝ)) ∞ (fun r : ℝ ↦ (Z, r)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact (hf.contMDiffAt (A.square_open.mem_nhds
    (A.square_contains ⟨Set.mem_univ _, hs⟩))).comp s hi.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_gammaSlice_contMDiffAt (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) (hτ : 0 < τ) (hmax : τ < τmax) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.gamma Z) τ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.gamma z.1 z.2) (Set.univ ×ˢ Set.Ioo 0 τmax) := by
    convert! A.gamma_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hi : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E × ℝ)) ∞ (fun r : ℝ ↦ (Z, r)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact (hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    ⟨Set.mem_univ _, hτ, hmax⟩)).comp τ hi.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_initialSlice_contMDiffAt (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) (hτ : 0 < τ) (hmax : τ < τmax) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContMDiffAt (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n) ∞ (fun V ↦ A.gamma V τ) Z := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.gamma z.1 z.2) (Set.univ ×ˢ Set.Ioo 0 τmax) := by
    convert! A.gamma_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hi : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E × ℝ)) ∞ (fun V : E ↦ (V, τ)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact (hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    ⟨Set.mem_univ _, hτ, hmax⟩)).comp Z hi.contMDiffAt

end PoincareConjecture.Proofs.M09
