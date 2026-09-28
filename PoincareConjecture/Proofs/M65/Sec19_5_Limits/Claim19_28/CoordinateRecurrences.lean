import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ProjectionRegularity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ChartPullback

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

noncomputable def m65ProjectedCoordinateJet (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (p : M) (i : ℕ) (t x : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1
    (P.charts.split (c x t) (m65IntrinsicTangentJet P.flow c i t x)).1

theorem m65ProjectedVelocity_eq_speed_smul (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    curveVelocity (n := n) (fun y => (c y t).1) x = curveSpeed P.flow c t x •
      (P.charts.split (c x t) (m65IntrinsicTangentJet P.flow c 0 t x)).1 := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hchain := mfderiv_comp_apply (f := fun y => c y t)
    (g := (Prod.fst : P.charts.Point → M)) x
    (hfst.mdifferentiableAt (by simp))
    ((hc.spatial_regular t ht x).mdifferentiableAt (by norm_num)) (1 : ℝ)
  change curveVelocity (n := n) (fun y => (c y t).1) x = _ at hchain
  rw [← P.charts.split_space] at hchain
  change curveVelocity (n := n) (fun y => (c y t).1) x =
    (P.charts.split (c x t) (curveVelocity (n := n + 1) (fun y => c y t) x)).1 at hchain
  rw [hchain]
  simp only [m65IntrinsicTangentJet, spatialUnitTangent, map_smul, Prod.smul_fst,
    smul_smul, mul_inv_cancel₀ (M62.speed_pos P.flow c hc ht x).ne', one_smul]

theorem m65ProjectedCoordinates_hasDerivAt (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    (p : M) {t x : ℝ} (ht : t ∈ Icc a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1)
      (curveSpeed P.flow c t x • m65ProjectedCoordinateJet P c p 0 t x) x := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => (c y t).1) x :=
    (hfst.mdifferentiableAt (by simp)).comp x
      ((hc.spatial_regular t ht x).mdifferentiableAt (by norm_num))
  have he := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hx
  have h : HasDerivAt (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1
        (curveVelocity (n := n) (fun y => (c y t).1) x)) x :=
    (he.hasMFDerivAt.comp x hgamma.hasMFDerivAt).hasFDerivAt.hasDerivAt
  rw [m65ProjectedVelocity_eq_speed_smul P c hc ht, map_smul] at h
  exact h

theorem m65ProjectedCoordinateJet_hasDerivAt [T2Space M]
    (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) (i : ℕ) :
    HasDerivAt (m65ProjectedCoordinateJet P c p i t)
      (curveSpeed P.flow c t x • m65ProjectedCoordinateJet P c p (i + 1) t x -
        M04.shiChartChristoffel (F.connection t) (chartAt (EuclideanSpace ℝ (Fin n)) p)
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1)
          (curveSpeed P.flow c t x • m65ProjectedCoordinateJet P c p 0 t x)
          (m65ProjectedCoordinateJet P c p i t x)) x := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ (fun y => c y t) :=
    hc.joint_smooth.comp_contMDiff (contDiff_id.prodMk contDiff_const).contMDiff
      (fun _ => ⟨mem_univ _, ht⟩)
  have hbase : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => (c y t).1) := hfst.comp hcurve
  have hjet : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent ∞
      (fun y => (⟨c y t, m65IntrinsicTangentJet P.flow c i t y⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point)) :=
    (m65IntrinsicTangentJet_joint_contMDiff c hc i).comp_contMDiff
      (contDiff_id.prodMk contDiff_const).contMDiff (fun _ => ⟨mem_univ _, ht⟩)
  have hpull := m65Projection_pullback P t (hjet.mdifferentiableAt (by simp) (x := x))
  rw [m65IntrinsicTangentJet_pullback c hc (Ioo_subset_Icc_self ht),
    map_smul, Prod.smul_fst] at hpull
  have h := m65Pullback_hasDerivAt_coordinates (F.connection t) p
    hbase (m65ProjectedTangentJet_spatial_contMDiff P c hc ht i) hx
  dsimp only at h
  rw [← hpull,
    m65ProjectedVelocity_eq_speed_smul P c hc (Ioo_subset_Icc_self ht), map_smul,
    map_smul] at h
  exact h

end PoincareConjecture
