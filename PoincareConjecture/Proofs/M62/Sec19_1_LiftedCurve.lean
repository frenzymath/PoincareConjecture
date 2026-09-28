import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeSlices
import PoincareConjecture.Proofs.M62.Lemma19_6_InteriorRegularity
import PoincareConjecture.Statements.M62CurveEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem liftCurve_smooth {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ∞ (G.liftCurve c) := by
  let := G.charts.chartedSpace
  let : ChartedSpace (ℝ × ℝ) (ℝ × ℝ) := prodChartedSpace ℝ ℝ ℝ ℝ
  have hcurve := hc.joint_smooth
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcurve
  have hj : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × OpenTime a b => (z.1, (z.2 : ℝ))) :=
    contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
  have hbase : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞
      (fun z : ℝ × OpenTime a b => c z.1 z.2) := by
    rw [← contMDiffOn_univ]
    exact hcurve.comp hj.contMDiffOn (fun z _ => ⟨mem_univ _, z.2.property⟩)
  exact G.charts.from_product_smooth.comp (hbase.prodMk contMDiff_snd)

theorem lifted_time {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c)
    (t : OpenTime a b) (x : ℝ) :
    G.liftedTimeVelocity c (x, t) =
      m62LiftedCurvature G c t x + G.charts.timeVector (G.liftCurve c (x, t)) := by
  let := G.charts.chartedSpace
  let : ChartedSpace (ℝ × ℝ) (ℝ × ℝ) := prodChartedSpace ℝ ℝ ℝ ℝ
  let I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)
  let j := fun z : ℝ × OpenTime a b => (z.1, (z.2 : ℝ))
  have hcurve := hc.joint_smooth
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcurve
  have hcd := (hcurve.contMDiffAt (x := (x, (t : ℝ)))
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, t.property⟩)).mdifferentiableAt
    (by simp)
  have hclockd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z : ℝ × OpenTime a b => (z.2 : ℝ)) (x, t) :=
    (contMDiff_subtype_val.comp contMDiff_snd).mdifferentiableAt (n := ∞) (by simp)
  have hclock : mfderiv I 𝓘(ℝ, ℝ)
      (fun z : ℝ × OpenTime a b => (z.2 : ℝ)) (x, t) (0, 1) = 1 := by
    have h := mfderiv_comp_apply
      (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (f := (Prod.snd : ℝ × OpenTime a b → OpenTime a b))
      (g := (Subtype.val : OpenTime a b → ℝ)) (x, t)
      (contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp))
      mdifferentiableAt_snd (0, 1)
    rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val, mfderiv_snd] at h
    exact h
  have hj : mfderiv I I j (x, t) (0, 1) = (0, 1) := by
    erw [mfderiv_prodMk mdifferentiableAt_fst hclockd]
    rw [mfderiv_fst]
    change (0, mfderiv I 𝓘(ℝ, ℝ)
      (fun z : ℝ × OpenTime a b => (z.2 : ℝ)) (x, t) (0, 1)) = (0, 1)
    rw [hclock]
  have hspatial : mfderiv I (𝓡 n)
      (fun z : ℝ × OpenTime a b => c z.1 z.2) (x, t) (0, 1) =
        m62CurvatureVector F c t x := by
    have h := mfderiv_comp_apply (I := I) (I' := I) (I'' := 𝓡 n)
      (f := j) (g := fun z : ℝ × ℝ => c z.1 z.2) (x, t) hcd
      (mdifferentiableAt_fst.prodMk hclockd) (0, 1)
    rw [hj, ← M08.curveVelocity_snd_eq_partialTangent _ hcd] at h
    exact h.trans (hc.equation t t.property x)
  have hb : MDifferentiableAt I (𝓡 n)
      (fun z : ℝ × OpenTime a b => c z.1 z.2) (x, t) :=
    ((G.charts.contMDiff_space.comp (G.liftCurve_smooth c hc)).mdifferentiableAt (by simp))
  have h := mfderiv_comp_apply
    (I := I) (I' := (𝓡 n).prod 𝓘(ℝ, ℝ)) (I'' := 𝓡 (n + 1))
    (f := fun z : ℝ × OpenTime a b => ((c z.1 z.2, z.2) : SpacetimeCarrier M a b))
    (g := (id : SpacetimeCarrier M a b → G.charts.Point)) (x, t)
    (G.charts.from_product_smooth.mdifferentiableAt (by simp))
    (hb.prodMk mdifferentiableAt_snd) (0, 1)
  apply (G.charts.split (G.liftCurve c (x, t))).injective
  change G.charts.split (G.liftCurve c (x, t))
    (mfderiv I (𝓡 (n + 1)) (id ∘ fun z : ℝ × OpenTime a b =>
      ((c z.1 z.2, z.2) : SpacetimeCarrier M a b)) (x, t) (0, 1)) = _
  rw [h]
  erw [G.charts.split_mfderiv_from_product]
  erw [mfderiv_prodMk hb mdifferentiableAt_snd]
  change (mfderiv I (𝓡 n) (fun z : ℝ × OpenTime a b => c z.1 z.2)
      (x, t) (0, 1),
    mfderiv I 𝓘(ℝ, ℝ) (Prod.snd : ℝ × OpenTime a b → OpenTime a b)
      (x, t) (0, 1)) = _
  rw [hspatial, mfderiv_snd]
  simp [m62LiftedCurvature, SpacetimeCharts.horizontal, SpacetimeCharts.timeVector]
  rfl

theorem lifted_spatial_velocity {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c)
    (t : OpenTime a b) (x : ℝ) :
    curveVelocity (fun y => G.liftCurve c (y, t)) x =
      G.charts.horizontal (G.liftCurve c (x, t))
        (curveVelocity (fun y => c y t) x) := by
  let := G.charts.chartedSpace
  have hgamma := (hc.spatial_regular t (Ioo_subset_Icc_self t.property)).mdifferentiableAt
    (x := x)
    (by norm_num)
  have h := mfderiv_comp_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) (I'' := 𝓡 (n + 1))
    (f := fun y : ℝ => c y t) (g := fun p : M => ((p, t) : G.charts.Point)) x
    ((G.charts.contMDiff_space_slice t).mdifferentiableAt (by simp)) hgamma (1 : ℝ)
  rw [G.charts.mfderiv_space_slice] at h
  exact h

end PoincareConjecture.M62.SpacetimeData
