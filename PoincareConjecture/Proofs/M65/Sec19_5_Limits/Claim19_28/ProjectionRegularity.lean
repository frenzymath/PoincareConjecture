import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.IntrinsicRecurrences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m65Projection_field_contMDiff (P : M62.CircleProductData F circumference)
    {gamma : ℝ → P.charts.Point}
    {Y : ∀ y, TangentSpace (𝓡 (n + 1)) (gamma y)}
    (hY : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent ∞
      (fun y => (⟨gamma y, Y y⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point))) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n).tangent ∞
      (fun y => (⟨(gamma y).1, (P.charts.split (gamma y) (Y y)).1⟩ :
        TangentBundle (𝓡 n) M)) := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have h := (hfst.contMDiff_tangentMap (m := ∞) (by simp)).comp hY
  intro x
  apply (h x).congr_of_eventuallyEq
  filter_upwards [] with y
  dsimp only [Function.comp_apply, tangentMap]
  rw [TotalSpace.mk_inj, ← P.charts.split_space]

theorem m65ProjectedTangentJet_spatial_contMDiff [T2Space M]
    (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n).tangent ∞
      (fun y => (⟨(c y t).1,
        (P.charts.split (c y t) (m65IntrinsicTangentJet P.flow c i t y)).1⟩ :
        TangentBundle (𝓡 n) M)) := by
  apply m65Projection_field_contMDiff P
  exact (m65IntrinsicTangentJet_joint_contMDiff c hc i).comp_contMDiff
    (contDiff_id.prodMk contDiff_const).contMDiff (fun _ => ⟨mem_univ _, ht⟩)

end PoincareConjecture
