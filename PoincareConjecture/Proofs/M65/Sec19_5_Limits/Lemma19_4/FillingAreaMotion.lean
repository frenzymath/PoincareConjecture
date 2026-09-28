import PoincareConjecture.Proofs.M09.TimeDependentFlow
import PoincareConjecture.Proofs.M09.OpenODEUniqueness
import PoincareConjecture.Proofs.M09.SmoothTangentChartPhase
import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M09.CompactFieldExtension
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.ImmersedAreaTransfer
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryArc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M65Filling

open Proofs.M09

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

private theorem triangular_bijective (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    Function.Bijective (fun z : ℝ × ℝ => (z.1, L z)) := by
  have hrep (z : ℝ × ℝ) : L z = z.1 * L (1, 0) + z.2 * L (0, 1) := by
    have heq : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
    conv_lhs => rw [heq]
    simp only [map_add, map_smul, smul_eq_mul]
  constructor
  · intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    change x.1 = y.1 at h1
    change L x = L y at h2
    rw [hrep x, hrep y, h1] at h2
    exact Prod.ext h1 (mul_right_cancel₀ hL (add_left_cancel h2))
  · intro y
    refine ⟨(y.1, (y.2 - y.1 * L (1, 0)) / L (0, 1)), ?_⟩
    refine Prod.ext rfl ?_
    change L (y.1, (y.2 - y.1 * L (1, 0)) / L (0, 1)) = y.2
    rw [hrep (y.1, (y.2 - y.1 * L (1, 0)) / L (0, 1))]
    dsimp only
    rw [div_mul_cancel₀ _ hL]
    ring

private theorem spacetime_inverse {h : ℝ × ℝ → ℝ} {O : Set (ℝ × ℝ)}
    (hO : IsOpen O) (hh : ContDiffOn ℝ ∞ h O) {z : ℝ × ℝ} (hz : z ∈ O)
    (hne : fderiv ℝ h z (0, 1) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (e : (ℝ × ℝ) → ℝ × ℝ) = (fun w => (w.1, h w)) ∧ z ∈ e.source ∧
      e.source ⊆ O ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let f : ℝ × ℝ → ℝ × ℝ := fun w => (w.1, h w)
  let L := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ h z)
  have hL : Function.Bijective L := triangular_bijective _ hne
  let E := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hL.1)
    (LinearMap.range_eq_top.mpr hL.2)
  have hhs := hh.contDiffAt (hO.mem_nhds hz)
  have hfs : ContDiffAt ℝ ∞ f z := contDiffAt_fst.prodMk hhs
  have hder : HasFDerivAt f (E : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) z :=
    hasFDerivAt_fst.prodMk ((hhs.differentiableAt (by simp)).hasFDerivAt)
  let e0 := hfs.toOpenPartialHomeomorph f hder (by simp)
  have hz0 : z ∈ e0.source := hfs.mem_toOpenPartialHomeomorph_source hder (by simp)
  let N := O ∩ (fun w => fderiv ℝ h w (0, 1)) ⁻¹' ({0}ᶜ)
  have hdc : ContinuousOn (fun w => fderiv ℝ h w (0, 1)) O :=
    (hh.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  have hN : IsOpen N := hdc.isOpen_inter_preimage hO isClosed_singleton.isOpen_compl
  let e := e0.restrOpen N hN
  have he : (e : (ℝ × ℝ) → ℝ × ℝ) = f := rfl
  refine ⟨e, he, ⟨hz0, hz, hne⟩, (fun _ hw => hw.2.1), ?_⟩
  intro y hy
  have hw := e.map_target hy
  have hhy := hh.contDiffAt (hO.mem_nhds hw.2.1)
  let Ly := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ h (e.symm y))
  have hLy := triangular_bijective (fderiv ℝ h (e.symm y)) hw.2.2
  let Ey := ContinuousLinearEquiv.ofBijective Ly (LinearMap.ker_eq_bot.mpr hLy.1)
    (LinearMap.range_eq_top.mpr hLy.2)
  have hdy : HasFDerivAt e (Ey : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (e.symm y) :=
    hasFDerivAt_fst.prodMk ((hhy.differentiableAt (by simp)).hasFDerivAt)
  exact (e.contDiffAt_symm hy hdy (contDiffAt_fst.prodMk hhy)).contDiffWithinAt

private theorem family_circle_continuous {J : Set ℝ}
    (loops : ℝ → C1FreeLoopSpace (M := M))
    (hc : ContinuousOn (fun z : ℝ × ℝ => periodicFreeLoop (loops z.2) z.1) (univ ×ˢ J)) :
    Continuous (fun z : J × LoopCircle => loops z.1 z.2) := by
  have ha : IsOpenQuotientMap m65LoopAngular :=
    ⟨m65LoopAngular_continuous_surjective.2, m65LoopAngular_continuous_surjective.1,
      m65LoopAngular_open⟩
  apply (IsOpenQuotientMap.id.prodMap ha).continuous_comp_iff.mp
  have he : ((fun z : J × LoopCircle => loops z.1 z.2) ∘ Prod.map id m65LoopAngular) =
      (fun z : J × ℝ => periodicFreeLoop (loops z.1) z.2) := by
    funext z
    exact ((loops z.1).boundary (m65LoopAngular z.2)).symm
  rw [he]
  exact hc.comp_continuous (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
    (fun z => ⟨mem_univ _, z.1.property⟩)

omit [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] in
private theorem moving_arc_capture [T2Space M] {J : Set ℝ} (hJ : IsOpen J)
    {c : J × LoopCircle → M} (hc : Continuous c) {q : J} {p : LoopCircle}
    (hinj : Function.Injective (fun x => c (q, x))) {A : Set LoopCircle}
    (hA : IsOpen A) (hp : p ∈ A) :
    ∃ U : Set (ℝ × M), IsOpen U ∧ ((q : ℝ), c (q, p)) ∈ U ∧
      U ⊆ J ×ˢ univ ∧ ∀ t : J, ∀ x : LoopCircle, ((t : ℝ), c (t, x)) ∈ U → x ∈ A := by
  let B : Set ((J × M) × LoopCircle) :=
    {z | z.2 ∈ Aᶜ ∧ c (z.1.1, z.2) = z.1.2}
  have hB : IsClosed B :=
    (hA.isClosed_compl.preimage continuous_snd).inter
      (isClosed_eq (hc.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
        (continuous_snd.comp continuous_fst))
  have hbad : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  let W : Set (J × M) := (Prod.fst '' B)ᶜ
  have hW : IsOpen W := hbad.isOpen_compl
  have hqW : (q, c (q, p)) ∈ W := by
    rintro ⟨⟨⟨t, y⟩, x⟩, ⟨hx, he⟩, heq⟩
    have ht : t = q := congrArg Prod.fst heq
    have hy : y = c (q, p) := congrArg Prod.snd heq
    subst t
    subst y
    exact hx (hinj he ▸ hp)
  let incl : J × M → ℝ × M := fun z => (z.1, z.2)
  have hi : IsOpenMap incl := hJ.isOpenMap_subtype_val.prodMap IsOpenMap.id
  refine ⟨incl '' W, hi W hW, mem_image_of_mem incl hqW, ?_, ?_⟩
  · rintro _ ⟨⟨t, y⟩, _, rfl⟩
    exact ⟨t.property, mem_univ y⟩
  · intro t x htx
    obtain ⟨⟨s, y⟩, hsy, he⟩ := htx
    have hst : s = t := Subtype.ext (congrArg Prod.fst he)
    have hy : y = c (t, x) := congrArg Prod.snd he
    subst s
    subst y
    by_contra hx
    exact hsy ⟨((t, c (t, x)), x), ⟨hx, rfl⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateField_smooth
    (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p) (T : Set ℝ)
    (hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (T ×ˢ univ))
    (p : M) :
    ContDiffOn ℝ ∞ (fun z : ℝ × LoopAmbient =>
      mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p)
        ((chartAt LoopAmbient p).symm z.2) (V z.1 ((chartAt LoopAmbient p).symm z.2)))
      (T ×ˢ (chartAt LoopAmbient p).target) := by
  have harg : ContMDiffOn 𝓘(ℝ, ℝ × LoopAmbient) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ∞
      (fun z : ℝ × LoopAmbient => (z.1, (chartAt LoopAmbient p).symm z.2))
      (T ×ˢ (chartAt LoopAmbient p).target) := by
    have h : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ∞
        (fun z : ℝ × LoopAmbient => (z.1, (chartAt LoopAmbient p).symm z.2))
        (T ×ˢ (chartAt LoopAmbient p).target) :=
      contMDiff_fst.contMDiffOn.prodMk
        (contMDiffOn_chart_symm.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
    convert! h using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hfield := hV.comp harg (fun _ hz => ⟨hz.1, mem_univ _⟩)
  have hchart := (tangentChartPhase_contMDiffOn p).comp hfield
    (fun z hz => (chartAt LoopAmbient p).map_target hz.2)
  exact hchart.contDiffOn.snd

set_option backward.isDefEq.respectTransparency false in
private theorem chartField_smooth (p : M) (U : Set (ℝ × M))
    (hsource : ∀ z ∈ U, z.2 ∈ (chartAt LoopAmbient p).source)
    (B : ℝ × M → LoopAmbient)
    (hB : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ B U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, chartVectorField p (B z) z.2⟩ : TangentBundle (𝓡 3) M)) U := by
  have hpair := (contMDiffOn_chart.comp contMDiff_snd.contMDiffOn hsource).prodMk hB
  have hmodel : ContMDiff ((𝓡 3).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : LoopAmbient × LoopAmbient => (⟨z.1, z.2⟩ : TangentBundle (𝓡 3) LoopAmbient)) := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓡 3) (n := ∞)) using 1
    rw [chartedSpaceSelf_prod]
    rfl
  have htv := hmodel.comp_contMDiffOn hpair
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (chartAt LoopAmbient p).symm (chartAt LoopAmbient p).target := contMDiffOn_chart_symm
  have ht := hc.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt LoopAmbient p).open_target.uniqueMDiffOn
  apply (ht.comp htv (fun z hz => (chartAt LoopAmbient p).map_source (hsource z hz))).congr
  intro z hz
  change (⟨z.2, chartVectorField p (B z) z.2⟩ : TangentBundle (𝓡 3) M) =
    ⟨(chartAt LoopAmbient p).symm ((chartAt LoopAmbient p) z.2),
      mfderivWithin (𝓡 3) (𝓡 3) (chartAt LoopAmbient p).symm (chartAt LoopAmbient p).target
        ((chartAt LoopAmbient p) z.2) (B z)⟩
  rw [mfderivWithin_of_isOpen (chartAt LoopAmbient p).open_target
    ((chartAt LoopAmbient p).map_source (hsource z hz))]
  have he := chartVectorField_at_inverse p (B z) ((chartAt LoopAmbient p) z.2)
    ((chartAt LoopAmbient p).map_source (hsource z hz))
  rw [(chartAt LoopAmbient p).left_inv (hsource z hz)] at he ⊢
  exact congrArg (Bundle.TotalSpace.mk' LoopAmbient z.2) he

set_option backward.isDefEq.respectTransparency false in
private theorem local_velocity_extension (c : ℝ × ℝ → M) (O : Set (ℝ × ℝ))
    (hO : IsOpen O) (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ c O)
    (z : ℝ × ℝ) (hz : z ∈ O)
    (hne : curveVelocity (n := 3) (fun x => c (z.1, x)) z.2 ≠ 0) :
    ∃ (U : Set (ℝ × M)) (Q : Set (ℝ × ℝ))
      (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p),
      IsOpen U ∧ IsOpen Q ∧ z ∈ Q ∧ Q ⊆ O ∧
      (∀ w ∈ Q, (w.1, c w) ∈ U) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun w : ℝ × M => (⟨w.2, V w.1 w.2⟩ : TangentBundle (𝓡 3) M)) U ∧
      ∀ w ∈ Q, V w.1 (c w) = curveVelocity (n := 3) (fun t => c (t, w.2)) w.1 := by
  let p := c z
  let chart := chartAt LoopAmbient p
  let S := O ∩ c ⁻¹' chart.source
  have hS : IsOpen S := hc.continuousOn.isOpen_inter_preimage hO chart.open_source
  have hzS : z ∈ S := ⟨hz, mem_chart_source _ _⟩
  let u : ℝ × ℝ → LoopAmbient := fun w => chart (c w)
  have hu : ContDiffOn ℝ ∞ u S :=
    (contMDiffOn_chart.comp (hc.mono inter_subset_left) (fun _ hw => hw.2)).contDiffOn
  have hds : DifferentiableAt ℝ u z :=
    (hu.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by simp)
  have hspArg : ContDiff ℝ ∞ (fun x : ℝ => (z.1, x)) := contDiff_const.prodMk contDiff_id
  have hspace : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (fun x => c (z.1, x)) z.2 :=
    ((hc.contMDiffAt (hO.mem_nhds hz)).comp z.2
      hspArg.contDiffAt.contMDiffAt).mdifferentiableAt (by simp)
  have hsp : HasDerivAt (fun x => u (z.1, x)) (fderiv ℝ u z (0, 1)) z.2 := by
    simpa only [Function.comp_def, id_eq] using hds.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have hcoord := hsp.unique (hasDerivAt_chart_curve p (fun x => c (z.1, x)) z.2 hzS.2 hspace)
  have hu0 : fderiv ℝ u z (0, 1) ≠ 0 := by
    intro he
    apply hne
    apply ((mdifferentiable_chart (I := 𝓡 3) p).mfderiv hzS.2).injective
    change mfderiv (𝓡 3) (𝓡 3) chart (c z)
      (curveVelocity (n := 3) (fun x => c (z.1, x)) z.2) =
      mfderiv (𝓡 3) (𝓡 3) chart (c z) 0
    rw [map_zero, ← hcoord, he]
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, fderiv ℝ u z (0, 1) j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hu0 (by ext j; exact hn j)
  let pr : LoopAmbient →L[ℝ] ℝ := EuclideanSpace.proj j
  let h : ℝ × ℝ → ℝ := fun w => pr (u w)
  have hh : ContDiffOn ℝ ∞ h S := pr.contDiff.comp_contDiffOn hu
  have hne' : fderiv ℝ h z (0, 1) ≠ 0 := by
    have hd := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
      (pr.hasFDerivAt.comp z hds.hasFDerivAt).fderiv
    change fderiv ℝ (pr ∘ u) z (0, 1) ≠ 0
    exact hd.trans_ne hj
  obtain ⟨e, he, hze, heS, hinv⟩ := spacetime_inverse hS hh hzS hne'
  let A : ℝ × M → ℝ × ℝ := fun w => (w.1, pr (chart w.2))
  let U : Set (ℝ × M) := (univ ×ˢ chart.source) ∩ A ⁻¹' e.target
  have hA : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, ℝ × ℝ) ∞ A
      (univ ×ˢ chart.source) := by
    have hhA : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞ A
        (univ ×ˢ chart.source) := contMDiff_fst.contMDiffOn.prodMk
      (pr.contDiff.contMDiff.comp_contMDiffOn
        (contMDiffOn_chart.comp contMDiff_snd.contMDiffOn (fun _ hw => hw.2)))
    convert! hhA using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hU : IsOpen U := hA.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod chart.open_source) e.open_target
  let B : ℝ × M → LoopAmbient := fun w => fderiv ℝ u (e.symm (A w)) (1, 0)
  have hparam := hinv.contMDiffOn.comp (hA.mono inter_subset_left) (fun _ hw => hw.2)
  have hdu : ContDiffOn ℝ ∞ (fun w => fderiv ℝ u w (1, 0)) S :=
    (hu.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  have hB : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞ B U :=
    hdu.contMDiffOn.comp hparam (fun _ hw => heS (e.map_target hw.2))
  let V := fun t p => chartVectorField (c z) (B (t, p)) p
  refine ⟨U, e.source, V, hU, e.open_source, hze, fun w hw => (heS hw).1, ?_,
    chartField_smooth p U (fun _ hw => hw.1.2) B hB, ?_⟩
  · intro w hw
    refine ⟨⟨mem_univ _, (heS hw).2⟩, ?_⟩
    change (w.1, pr (chart (c w))) ∈ e.target
    simpa only [he, h, u] using e.map_source hw
  · intro w hw
    have heA : A (w.1, c w) = e w := by rw [he]
    change chartVectorField p (fderiv ℝ u (e.symm (A (w.1, c w))) (1, 0)) (c w) = _
    rw [heA, e.left_inv hw]
    have hcw := hc.contMDiffAt (hO.mem_nhds (heS hw).1)
    have htimeArg : ContDiff ℝ ∞ (fun t : ℝ => (t, w.2)) := contDiff_id.prodMk contDiff_const
    have hct : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (fun t => c (t, w.2)) w.1 :=
      (hcw.comp w.1 htimeArg.contDiffAt.contMDiffAt).mdifferentiableAt (by simp)
    have hud : DifferentiableAt ℝ u w :=
      (hu.contDiffAt (hS.mem_nhds (heS hw))).differentiableAt (by simp)
    apply chartVectorField_coordinate_velocity p (fun t => c (t, w.2)) w.1
      (fderiv ℝ u w (1, 0)) (heS hw).2 hct
    simpa only [Function.comp_def, id_eq] using hud.hasFDerivAt.comp_hasDerivAt w.1
      ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))

set_option backward.isDefEq.respectTransparency false in
private theorem moving_velocity_extension [T2Space M] {J : Set ℝ} (hJ : IsOpen J)
    (loops : ℝ → C1FreeLoopSpace (M := M))
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞
      (fun w : ℝ × ℝ => periodicFreeLoop (loops w.1) w.2) (J ×ˢ univ))
    (q : ℝ) (hq : q ∈ J) (hinj : Function.Injective (loops q : LoopCircle → M))
    (x : ℝ) (hne : curveVelocity (n := 3) (periodicFreeLoop (loops q)) x ≠ 0) :
    ∃ (U : Set (ℝ × M)) (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p),
      IsOpen U ∧ (q, periodicFreeLoop (loops q) x) ∈ U ∧ U ⊆ J ×ˢ univ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun w : ℝ × M => (⟨w.2, V w.1 w.2⟩ : TangentBundle (𝓡 3) M)) U ∧
      ∀ t y : ℝ, (t, periodicFreeLoop (loops t) y) ∈ U →
        V t (periodicFreeLoop (loops t) y) =
          curveVelocity (n := 3) (fun s => periodicFreeLoop (loops s) y) t := by
  let c : ℝ × ℝ → M := fun w => periodicFreeLoop (loops w.1) w.2
  obtain ⟨U₀, Q, V, hU₀, hQ, hqx, hQsub, hgraph, hV, hagree⟩ :=
    local_velocity_extension c (J ×ˢ univ) (hJ.prod isOpen_univ) hc (q, x)
      ⟨hq, mem_univ _⟩ hne
  obtain ⟨T₀, hT₀, X₀, hX₀, hTX₀⟩ := mem_nhds_prod_iff.mp (hQ.mem_nhds hqx)
  obtain ⟨T, hTT₀, hT, hqT⟩ := mem_nhds_iff.mp hT₀
  obtain ⟨X, hXX₀, hX, hxX⟩ := mem_nhds_iff.mp hX₀
  have hTX : T ×ˢ X ⊆ Q := fun _ hw => hTX₀ ⟨hTT₀ hw.1, hXX₀ hw.2⟩
  have hcircle : Continuous (fun w : J × LoopCircle => loops w.1 w.2) := by
    apply family_circle_continuous loops
    exact hc.continuousOn.comp continuous_swap.continuousOn (fun _ hw => ⟨hw.2, hw.1⟩)
  have harceq (s y : ℝ) : loops s (m65LoopAngular y) = c (s, y) :=
    ((loops s).boundary (m65LoopAngular y)).symm
  obtain ⟨U₁, hU₁, hqU₁, hU₁sub, hcap⟩ := moving_arc_capture hJ hcircle
    (q := ⟨q, hq⟩) (p := m65LoopAngular x) hinj (m65LoopAngular_open X hX)
    (mem_image_of_mem m65LoopAngular hxX)
  let U := U₀ ∩ U₁ ∩ (T ×ˢ univ)
  have hU : IsOpen U := (hU₀.inter hU₁).inter (hT.prod isOpen_univ)
  have hqU : (q, c (q, x)) ∈ U :=
    ⟨⟨hgraph _ hqx, by simpa only [harceq] using hqU₁⟩, hqT, mem_univ _⟩
  refine ⟨U, V, hU, hqU, fun _ hw => hU₁sub hw.1.2,
    hV.mono (inter_subset_left.trans inter_subset_left), ?_⟩
  intro t y hty
  have htJ : t ∈ J := (hU₁sub hty.1.2).1
  have hty' : (t, loops t (m65LoopAngular y)) ∈ U₁ := by
    simpa only [harceq] using hty.1.2
  obtain ⟨z, hzX, hzy⟩ := hcap ⟨t, htJ⟩ (m65LoopAngular y) hty'
  have hcurves : (fun s => c (s, z)) = (fun s => c (s, y)) := by
    funext s
    rw [← harceq, ← harceq, hzy]
  have htz := hagree (t, z) (hTX ⟨hty.2.1, hzX⟩)
  change V t (c (t, z)) = curveVelocity (n := 3) (fun s => c (s, z)) t at htz
  rw [congrFun hcurves t, hcurves] at htz
  exact htz

set_option backward.isDefEq.respectTransparency false in
private theorem local_motion
    (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p) (T : Set ℝ) (hT : IsOpen T)
    (hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (T ×ˢ univ))
    (q : ℝ) (hq : q ∈ T) (p : M) :
    ∃ (W : Set M) (d : ℝ) (phi : M × ℝ → M),
      IsOpen W ∧ p ∈ W ∧ 0 < d ∧
      ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ phi (W ×ˢ Ioo (-d) d) ∧
      (∀ y ∈ W, phi (y, 0) = y) ∧
      ∀ y ∈ W, ∀ s ∈ Ioo (-d) d,
        q + s ∈ T ∧ MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (fun r => phi (y, r)) s ∧
          curveVelocity (n := 3) (fun r => phi (y, r)) s = V (q + s) (phi (y, s)) := by
  let c := chartAt LoopAmbient p
  let v : ℝ × LoopAmbient → LoopAmbient := fun z =>
    mfderiv (𝓡 3) (𝓡 3) c (c.symm z.2) (V z.1 (c.symm z.2))
  obtain ⟨beta, Q, d, hQ, hpQ, hQS, hd, hbeta, hzero, hode⟩ :=
    exists_local_smooth_timeDependent_flow (T ×ˢ c.target) (hT.prod c.open_target)
      v (coordinateField_smooth V T hV p) (q, c p) ⟨hq, c.map_source (mem_chart_source _ _)⟩
  let W : Set M := c.source ∩ (fun y => (q, c y)) ⁻¹' Q
  let phi : M × ℝ → M := fun z => c.symm (beta ((q, c z.1), z.2))
  have hW : IsOpen W := (continuousOn_const.prodMk c.continuousOn).isOpen_inter_preimage
    c.open_source hQ
  have hpW : p ∈ W := ⟨mem_chart_source _ _, hpQ⟩
  have harg : ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) 𝓘(ℝ, (ℝ × LoopAmbient) × ℝ) ∞
      (fun z : M × ℝ => ((q, c z.1), z.2)) (W ×ˢ Ioo (-d) d) := by
    have hin : ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ × LoopAmbient) ∞
        (fun z : M × ℝ => (q, c z.1)) (W ×ˢ Ioo (-d) d) := by
      have h : ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ∞
          (fun z : M × ℝ => (q, c z.1)) (W ×ˢ Ioo (-d) d) :=
        contMDiffOn_const.prodMk
          (contMDiffOn_chart.comp contMDiff_fst.contMDiffOn (fun _ hz => hz.1.1))
      convert! h using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    convert! hin.prodMk contMDiff_snd.contMDiffOn using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hb : ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞
      (fun z : M × ℝ => beta ((q, c z.1), z.2)) (W ×ˢ Ioo (-d) d) :=
    hbeta.contMDiffOn.comp harg (fun _ hz => ⟨hz.1.2, hz.2⟩)
  have hphi : ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞
      phi (W ×ˢ Ioo (-d) d) :=
    contMDiffOn_chart_symm.comp hb (fun z hz => (hode _ hz.1.2 _ hz.2).1.2)
  refine ⟨W, d, phi, hW, hpW, hd, hphi, ?_, ?_⟩
  · intro y hy
    exact (congrArg c.symm (hzero (q, c y) hy.2)).trans (c.left_inv hy.1)
  · intro y hy s hs
    have ho := hode (q, c y) hy.2 s hs
    have hc := (mdifferentiable_chart (I := 𝓡 3) p).mdifferentiableAt_symm ho.1.2
    have ha := ho.2.differentiableAt.mdifferentiableAt
    refine ⟨ho.1.1, hc.comp s ha, ?_⟩
    have hv := curveVelocityWithin_inverseChart p (fun r => beta ((q, c y), r))
      univ s (v (q + s, beta ((q, c y), s))) (uniqueDiffWithinAt_univ) ho.2 ho.1.2
    simp only [curveVelocityWithin, mfderivWithin_univ] at hv
    change curveVelocity (n := 3) (fun r => c.symm (beta ((q, c y), r))) s =
      mfderiv (𝓡 3) (𝓡 3) c.symm (beta ((q, c y), s))
        (v (q + s, beta ((q, c y), s))) at hv
    change curveVelocity (n := 3) (fun r => c.symm (beta ((q, c y), r))) s = _
    rw [hv]
    rw [← chartVectorField_at_inverse p _ _ ho.1.2]
    exact chartVectorField_differential p _ _ (c.map_target ho.1.2)

set_option backward.isDefEq.respectTransparency false in
private theorem motion_eventuallyEq
    (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p) (T : Set ℝ) (hT : IsOpen T)
    (hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (T ×ˢ univ))
    (f g : ℝ → M) (q : ℝ) (hq : q ∈ T) (heq : f q = g q)
    (hf : ∀ᶠ t in 𝓝 q, t ∈ T ∧ MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) f t ∧
      curveVelocity (n := 3) f t = V t (f t))
    (hg : ∀ᶠ t in 𝓝 q, t ∈ T ∧ MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) g t ∧
      curveVelocity (n := 3) g t = V t (g t)) : f =ᶠ[𝓝 q] g := by
  let p := f q
  let c := chartAt LoopAmbient p
  let v : ℝ × LoopAmbient → LoopAmbient := fun z =>
    mfderiv (𝓡 3) (𝓡 3) c (c.symm z.2) (V z.1 (c.symm z.2))
  have hp : f q ∈ c.source := mem_chart_source _ _
  have hfc : ∀ᶠ t in 𝓝 q, f t ∈ c.source :=
    hf.self_of_nhds.2.1.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hp)
  have hgc : ∀ᶠ t in 𝓝 q, g t ∈ c.source :=
    hg.self_of_nhds.2.1.continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds (heq ▸ hp))
  have hf' : ∀ᶠ t in 𝓝 q, (t, c (f t)) ∈ T ×ˢ c.target ∧
      HasDerivAt (fun s => c (f s)) (v (t, c (f t))) t := by
    filter_upwards [hf, hfc] with t ht hc
    refine ⟨⟨ht.1, c.map_source hc⟩, ?_⟩
    have hh := hasDerivAt_chart_curve p f t hc ht.2.1
    change HasDerivAt (fun s => c (f s))
      (mfderiv (𝓡 3) (𝓡 3) c (c.symm (c (f t))) (V t (c.symm (c (f t))))) t
    rw [c.left_inv hc]
    simpa only [ht.2.2] using hh
  have hg' : ∀ᶠ t in 𝓝 q, (t, c (g t)) ∈ T ×ˢ c.target ∧
      HasDerivAt (fun s => c (g s)) (v (t, c (g t))) t := by
    filter_upwards [hg, hgc] with t ht hc
    refine ⟨⟨ht.1, c.map_source hc⟩, ?_⟩
    have hh := hasDerivAt_chart_curve p g t hc ht.2.1
    change HasDerivAt (fun s => c (g s))
      (mfderiv (𝓡 3) (𝓡 3) c (c.symm (c (g t))) (V t (c.symm (c (g t))))) t
    rw [c.left_inv hc]
    simpa only [ht.2.2] using hh
  have he := openODE_eventuallyEq (T ×ˢ c.target) (hT.prod c.open_target) v
    ((coordinateField_smooth V T hV p).of_le (by simp))
    (fun t => c (f t)) (fun t => c (g t)) q ⟨hq, c.map_source hp⟩
    (congrArg c heq) hf' hg'
  filter_upwards [he, hfc, hgc] with t ht hf hg
  exact c.injOn hf hg ht

theorem motion_eqOn [T2Space M]
    (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p) (T : Set ℝ) (hT : IsOpen T)
    (hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (T ×ˢ univ))
    (I : Set ℝ) (hI : IsOpen I) (hconn : IsPreconnected I) (hIT : I ⊆ T)
    (f g : ℝ → M) (q : ℝ) (hq : q ∈ I) (heq : f q = g q)
    (hf : ∀ t ∈ I, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) f t ∧
      curveVelocity (n := 3) f t = V t (f t))
    (hg : ∀ t ∈ I, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) g t ∧
      curveVelocity (n := 3) g t = V t (g t)) : EqOn f g I := by
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hconn
  let A : Set I := {t | f t = g t}
  have hfc : ContinuousOn f I := fun t ht => (hf t ht).1.continuousAt.continuousWithinAt
  have hgc : ContinuousOn g I := fun t ht => (hg t ht).1.continuousAt.continuousWithinAt
  have hclosed : IsClosed A := isClosed_eq hfc.domRestrict hgc.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hf' : ∀ᶠ r in 𝓝 (t : ℝ), r ∈ T ∧ MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) f r ∧
        curveVelocity (n := 3) f r = V r (f r) :=
      Filter.Eventually.mono (hI.mem_nhds t.property) (fun r hr => ⟨hIT hr, hf r hr⟩)
    have hg' : ∀ᶠ r in 𝓝 (t : ℝ), r ∈ T ∧ MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) g r ∧
        curveVelocity (n := 3) g r = V r (g r) :=
      Filter.Eventually.mono (hI.mem_nhds t.property) (fun r hr => ⟨hIT hr, hg r hr⟩)
    exact continuousAt_subtype_val.preimage_mem_nhds
      (motion_eventuallyEq V T hT hV f g t (hIT t.property) ht hf' hg')
  have hAll : A = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨q, hq⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : I) ∈ A := by rw [hAll]; exact mem_univ _
  exact hm

set_option backward.isDefEq.respectTransparency false in

theorem compact_motion [T2Space M]
    (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p) (T : Set ℝ) (hT : IsOpen T)
    (hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (T ×ˢ univ))
    (q : ℝ) (hq : q ∈ T) (K : Set M) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ (G : Set M) (d : ℝ) (Phi : M × ℝ → M),
      IsOpen G ∧ K ⊆ G ∧ 0 < d ∧ (∀ s ∈ Ioo (-d) d, q + s ∈ T) ∧
      ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ Phi (G ×ˢ Ioo (-d) d) ∧
      (∀ y ∈ G, Phi (y, 0) = y) ∧
      ∀ y ∈ G, ∀ s ∈ Ioo (-d) d,
        MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Phi (y, r)) s ∧
          curveVelocity (n := 3) (fun r => Phi (y, r)) s = V (q + s) (Phi (y, s)) := by
  classical
  choose W d phi hW hp hd hphi hzero hode using (fun p => local_motion V T hT hV q hq p)
  obtain ⟨S, hcover⟩ := hK.elim_finite_subcover W hW
    (fun p _ => mem_iUnion.mpr ⟨p, hp p⟩)
  have hS : S.Nonempty := by
    obtain ⟨p, hpK⟩ := hne
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (hcover hpK)
    exact ⟨i, hi⟩
  let δ := S.inf' hS d
  have hδ : 0 < δ := (Finset.lt_inf'_iff hS).mpr (fun i _ => hd i)
  have hδd (i : M) (hi : i ∈ S) : δ ≤ d i := Finset.inf'_le d hi
  have hsmall (i : M) (hi : i ∈ S) : Ioo (-δ) δ ⊆ Ioo (-(d i)) (d i) := by
    intro s hs
    exact ⟨lt_of_le_of_lt (neg_le_neg (hδd i hi)) hs.1, hs.2.trans_le (hδd i hi)⟩
  let G : Set M := ⋃ i ∈ S, W i
  have hG : IsOpen G := isOpen_biUnion (fun i _ => hW i)
  have hchoose (y : G) : ∃ i, i ∈ S ∧ (y : M) ∈ W i := by
    obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp y.property
    exact ⟨i, hi, hy⟩
  choose idx hidxS hidxW using hchoose
  let Phi : M × ℝ → M := fun z => if h : z.1 ∈ G then phi (idx ⟨z.1, h⟩) z else z.1
  let T' : Set ℝ := (fun s => q + s) ⁻¹' T
  let V' := fun s p => V (q + s) p
  have hT' : IsOpen T' := hT.preimage (continuous_const.add continuous_id)
  have hV' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, V' z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (T' ×ˢ univ) :=
    hV.comp ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      (fun _ hz => ⟨hz.1, mem_univ _⟩)
  have htime : ∀ s ∈ Ioo (-δ) δ, q + s ∈ T := by
    obtain ⟨i, hi⟩ := hS
    intro s hs
    exact (hode i i (hp i) s (hsmall i hi hs)).1
  have hzeroδ : (0 : ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hoverlap (i j y : M) (hi : i ∈ S) (hj : j ∈ S)
      (hyi : y ∈ W i) (hyj : y ∈ W j) :
      EqOn (fun s => phi i (y, s)) (fun s => phi j (y, s)) (Ioo (-δ) δ) := by
    apply motion_eqOn V' T' hT' hV' (Ioo (-δ) δ) isOpen_Ioo isPreconnected_Ioo
      (fun s hs => htime s hs) _ _ 0 hzeroδ
      ((hzero i y hyi).trans (hzero j y hyj).symm)
    · intro s hs
      exact (hode i y hyi s (hsmall i hi hs)).2
    · intro s hs
      exact (hode j y hyj s (hsmall j hj hs)).2
  have heq (i : M) (hi : i ∈ S) (y : M) (hy : y ∈ W i) (s : ℝ) (hs : s ∈ Ioo (-δ) δ) :
      Phi (y, s) = phi i (y, s) := by
    have hyG : y ∈ G := mem_iUnion₂.mpr ⟨i, hi, hy⟩
    change (if h : y ∈ G then phi (idx ⟨y, h⟩) (y, s) else y) = _
    rw [dif_pos hyG]
    exact hoverlap _ i y (hidxS ⟨y, hyG⟩) hi (hidxW ⟨y, hyG⟩) hy hs
  refine ⟨G, δ, Phi, hG, hcover, hδ, htime, ?_, ?_, ?_⟩
  · intro z hz
    let i := idx ⟨z.1, hz.1⟩
    have hi := hidxS ⟨z.1, hz.1⟩
    have hzW := hidxW ⟨z.1, hz.1⟩
    have hlocal := (hphi i).contMDiffAt
      ((hW i).prod isOpen_Ioo |>.mem_nhds ⟨hzW, hsmall i hi hz.2⟩)
    have hevent : Phi =ᶠ[𝓝 z] phi i := by
      filter_upwards [(hW i |>.prod isOpen_Ioo).mem_nhds ⟨hzW, hz.2⟩] with w hw
      exact heq i hi w.1 hw.1 w.2 hw.2
    exact (hlocal.congr_of_eventuallyEq hevent).contMDiffWithinAt
  · intro y hy
    exact (heq _ (hidxS ⟨y, hy⟩) y (hidxW ⟨y, hy⟩) 0 hzeroδ).trans
      (hzero _ y (hidxW ⟨y, hy⟩))
  · intro y hy s hs
    let i := idx ⟨y, hy⟩
    have hi := hidxS ⟨y, hy⟩
    have hyW := hidxW ⟨y, hy⟩
    have hh := (hode i y hyW s (hsmall i hi hs)).2
    have hevent : (fun r => Phi (y, r)) =ᶠ[𝓝 s] (fun r => phi i (y, r)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact heq i hi y hyW r hr
    refine ⟨hh.1.congr_of_eventuallyEq hevent, ?_⟩
    have hder := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 3) (Phi (y, s)) => L 1)
      (hevent.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
    exact hder.trans (hh.2.trans (congrArg (fun p => (V (q + s) p : LoopAmbient))
      hevent.self_of_nhds.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem spacetime_weightedField_smooth {ι : Type*} [Fintype ι]
    (U : ι → Set (ℝ × M)) (hU : ∀ i, IsOpen (U i))
    (ρ : ι → ℝ × M → ℝ)
    (hρ : ∀ i, ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ (ρ i))
    (hsupp : ∀ i, tsupport (ρ i) ⊆ U i)
    (X : ι → ℝ → (p : M) → TangentSpace (𝓡 3) p)
    (hX : ∀ i, ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, X i z.1 z.2⟩ : TangentBundle (𝓡 3) M)) (U i)) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun z : ℝ × M => (⟨z.2, ∑ i, ρ i z • X i z.1 z.2⟩ : TangentBundle (𝓡 3) M)) := by
  let P := (𝓘(ℝ, ℝ)).prod (𝓡 3)
  let A : ι → (z : ℝ × M) → TangentSpace P z := fun i z => (0, X i z.1 z.2)
  have hA (i : ι) : ContMDiff P (P.prod 𝓘(ℝ, ℝ × LoopAmbient)) ∞
      (fun z : ℝ × M => (⟨z, ρ i z • A i z⟩ : TangentBundle P (ℝ × M))) :=
    (hρ i).contMDiffOn.smul_section_of_tsupport (hU i) (hsupp i)
      (parametricField_lift_smooth (X i) (U i) (hX i))
  have hsum : ContMDiff P (P.prod 𝓘(ℝ, ℝ × LoopAmbient)) ∞
      (fun z : ℝ × M => (⟨z, ∑ i, ρ i z • A i z⟩ : TangentBundle P (ℝ × M))) :=
    ContMDiff.sum_section (fun i _ => hA i)
  have hproj : ContMDiff (P.prod 𝓘(ℝ, ℝ × LoopAmbient)) ((𝓡 3).prod (𝓡 3)) ∞
      (tangentMap P (𝓡 3) (@Prod.snd ℝ M)) :=
    (contMDiff_snd (n := ∞)).contMDiff_tangentMap (by simp)
  apply (hproj.comp hsum).congr
  intro z
  change (⟨z.2, ∑ i, ρ i z • X i z.1 z.2⟩ : TangentBundle (𝓡 3) M) =
    tangentMap ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) (@Prod.snd ℝ M)
      ⟨z, ∑ i, ρ i z • A i z⟩
  rw [tangentMap_prodSnd]
  apply congrArg (fun v : TangentSpace (𝓡 3) z.2 => (⟨z.2, v⟩ : TangentBundle (𝓡 3) M))
  change (∑ i, ρ i z • X i z.1 z.2) = (∑ i, ρ i z • A i z).2
  calc
    _ = ∑ i, (ContinuousLinearMap.snd ℝ ℝ LoopAmbient) (ρ i z • A i z) := rfl
    _ = _ := (map_sum (ContinuousLinearMap.snd ℝ ℝ LoopAmbient) _ _).symm

set_option backward.isDefEq.respectTransparency false in

theorem family_velocity_extension [T2Space M] [SigmaCompactSpace M]
    {J : Set ℝ} (hJ : IsOpen J) (loops : ℝ → C1FreeLoopSpace (M := M))
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞
      (fun w : ℝ × ℝ => periodicFreeLoop (loops w.1) w.2) (J ×ˢ univ))
    (q : ℝ) (hq : q ∈ J) (hinj : Function.Injective (loops q : LoopCircle → M))
    (hreg : ∀ x, curveVelocity (n := 3) (periodicFreeLoop (loops q)) x ≠ 0) :
    ∃ (T : Set ℝ) (V : (t : ℝ) → (p : M) → TangentSpace (𝓡 3) p),
      IsOpen T ∧ q ∈ T ∧ T ⊆ J ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun w : ℝ × M => (⟨w.2, V w.1 w.2⟩ : TangentBundle (𝓡 3) M)) ∧
      ∀ t ∈ T, ∀ x : ℝ, V t (periodicFreeLoop (loops t) x) =
        curveVelocity (n := 3) (fun s => periodicFreeLoop (loops s) x) t := by
  classical
  have hlocal (p : LoopCircle) :
      ∃ (U : Set (ℝ × M)) (V : (t : ℝ) → (y : M) → TangentSpace (𝓡 3) y),
        IsOpen U ∧ (q, loops q p) ∈ U ∧ U ⊆ J ×ˢ univ ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
          (fun w : ℝ × M => (⟨w.2, V w.1 w.2⟩ : TangentBundle (𝓡 3) M)) U ∧
        ∀ t x : ℝ, (t, periodicFreeLoop (loops t) x) ∈ U →
          V t (periodicFreeLoop (loops t) x) =
            curveVelocity (n := 3) (fun s => periodicFreeLoop (loops s) x) t := by
    obtain ⟨x, rfl⟩ := m65LoopAngular_continuous_surjective.2 p
    have he : loops q (m65LoopAngular x) = periodicFreeLoop (loops q) x :=
      ((loops q).boundary (m65LoopAngular x)).symm
    rw [he]
    exact moving_velocity_extension hJ loops hc q hq hinj x (hreg x)
  choose U X hU hcenter hUJ hX hagree using hlocal
  let K : Set (ℝ × M) := range (fun p : LoopCircle => (q, loops q p))
  have hK : IsCompact K := isCompact_range (continuous_const.prodMk (loops q).continuous)
  obtain ⟨S, hcover⟩ := hK.elim_finite_subcover U hU (by
    rintro _ ⟨p, rfl⟩
    exact mem_iUnion.mpr ⟨p, hcenter p⟩)
  let O : Option S → Set (ℝ × M) := fun i => i.elim Kᶜ (fun p => U p)
  let Y : Option S → ℝ → (p : M) → TangentSpace (𝓡 3) p :=
    fun i => i.elim (fun _ _ => 0) (fun p => X p)
  have hO : ∀ i, IsOpen (O i) := fun i => by
    cases i with
    | none => exact hK.isClosed.isOpen_compl
    | some p => exact hU p
  have hfull : univ ⊆ ⋃ i, O i := by
    intro w _
    by_cases hw : w ∈ K
    · obtain ⟨p, hp, hwU⟩ := mem_iUnion₂.mp (hcover hw)
      exact mem_iUnion.mpr ⟨some ⟨p, hp⟩, hwU⟩
    · exact mem_iUnion.mpr ⟨none, hw⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    ((𝓘(ℝ, ℝ)).prod (𝓡 3)) isClosed_univ O hO hfull
  have hY (i : Option S) :
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun w : ℝ × M => (⟨w.2, Y i w.1 w.2⟩ : TangentBundle (𝓡 3) M)) (O i) := by
    cases i with
    | none => exact ((Bundle.contMDiff_zeroSection (IB := 𝓡 3) (F := LoopAmbient)
        (𝕜 := ℝ) (E := TangentSpace (𝓡 3))).comp contMDiff_snd).contMDiffOn
    | some p => exact hX p
  let V := fun t p => ∑ i : Option S, ρ i (t, p) • Y i t p
  have hV := spacetime_weightedField_smooth O hO (fun i => ρ i)
    (fun i => (ρ i).contMDiff) hρ Y hY
  let N : Set (ℝ × M) := (tsupport (ρ none))ᶜ
  have hN : IsOpen N := (isClosed_tsupport _).isOpen_compl
  have hKN : K ⊆ N := fun w hw hws => hρ none hws hw
  have hvelocity (t x : ℝ) (htx : (t, periodicFreeLoop (loops t) x) ∈ N) :
      V t (periodicFreeLoop (loops t) x) =
        curveVelocity (n := 3) (fun s => periodicFreeLoop (loops s) x) t := by
    have hsum : ∑ i : Option S, ρ i (t, periodicFreeLoop (loops t) x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using
        ρ.sum_eq_one (mem_univ (t, periodicFreeLoop (loops t) x))
    change (∑ i : Option S, ρ i (t, periodicFreeLoop (loops t) x) •
      Y i t (periodicFreeLoop (loops t) x)) = _
    calc
      _ = ∑ i : Option S, ρ i (t, periodicFreeLoop (loops t) x) •
          curveVelocity (n := 3) (fun s => periodicFreeLoop (loops s) x) t := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : ρ i (t, periodicFreeLoop (loops t) x) = 0
        · simp only [hi, zero_smul]
        · have hmem := hρ i (subset_tsupport (ρ i) (Function.mem_support.mpr hi))
          cases i with
          | none => exact False.elim (htx (subset_tsupport (ρ none) (Function.mem_support.mpr hi)))
          | some p => rw [show Y (some p) t (periodicFreeLoop (loops t) x) =
                curveVelocity (n := 3) (fun s => periodicFreeLoop (loops s) x) t from
              hagree p t x hmem]
      _ = _ := by rw [← Finset.sum_smul, hsum, one_smul]
  have hcirc : Continuous (fun w : J × LoopCircle => loops w.1 w.2) :=
    family_circle_continuous loops
      (hc.continuousOn.comp continuous_swap.continuousOn (fun _ hw => ⟨hw.2, hw.1⟩))
  have hnear : ∀ᶠ t : J in 𝓝 ⟨q, hq⟩, ∀ p : LoopCircle, ((t : ℝ), loops t p) ∈ N := by
    have hh := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := (⟨q, hq⟩ : J)) (P := fun t : J => fun p : LoopCircle =>
        ((t : ℝ), loops t p) ∈ N) (fun p (_ : p ∈ (univ : Set LoopCircle)) =>
        (hN.preimage ((continuous_subtype_val.comp continuous_fst).prodMk hcirc)).mem_nhds
          (show ((q : ℝ), loops q p) ∈ N from hKN ⟨p, rfl⟩))
    simpa only [mem_univ, forall_true_left] using hh
  obtain ⟨B, hBsub, hB, hqB⟩ := mem_nhds_iff.mp hnear
  refine ⟨Subtype.val '' B, V, hJ.isOpenMap_subtype_val B hB, ⟨⟨q, hq⟩, hqB, rfl⟩,
    (by rintro t ⟨s, _, rfl⟩; exact s.property), hV, ?_⟩
  rintro t ⟨s, hs, rfl⟩ x
  apply hvelocity
  have he : loops s (m65LoopAngular x) = periodicFreeLoop (loops s) x :=
    ((loops s).boundary (m65LoopAngular x)).symm
  simpa only [he] using hBsub hs (m65LoopAngular x)

end PoincareConjecture.M65Filling
