import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Level.RegularBand
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Reverse
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import Mathlib.Geometry.Manifold.Diffeomorph













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem normalizedGradient_neg
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) :
    D.normalizedGradient (fun y => -f y) x = -D.normalizedGradient f x := by
  have hg : D.gradient (fun y => -f y) x = -D.gradient f x := by
    have hh := D.gradient_comp hf (differentiableAt_id.neg)
    have hd : deriv (fun r : ℝ => -r) (f x) = -1 := (hasDerivAt_id (f x)).neg.deriv
    change D.gradient (fun y => -f y) x = deriv (fun r : ℝ => -r) (f x) • D.gradient f x at hh
    simpa only [hd, neg_one_smul] using hh
  simp only [normalizedGradient, hg, map_neg, neg_apply, neg_neg, smul_neg]
end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData
open Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow

theorem contMDiffOn_normalizedGradient_of_regular
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (D.normalizedGradient f)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  have hgrad := D.contMDiffAt_gradient (hf.contMDiffAt (hU.mem_nhds hx))
  have hpair : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x :=
    hgrad.inner_bundle hgrad
  have hnonzero : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0 :=
    fun hz => hreg x hx ((gradient_energy_eq_zero_iff_mfderiv_eq_zero_manifold D f x).mp hz)
  exact (((contDiffAt_inv ℝ hnonzero).contMDiffAt.comp x hpair).smul_section hgrad).contMDiffWithinAt
end PoincareConjecture.LeviCivitaData

open TopologicalSpace Poincare.Geometry.Manifold.RegularLevel
namespace PoincareConjecture.LeviCivitaData

local instance {n : ℕ} : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩




theorem exists_level_diffeomorphisms_on_compact_regular_band
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : RiemannianMetric (n + 1) M} (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b : ℝ} (hab : a ≤ b) (hband : IsCompact {x | x ∈ U ∧ f x ∈ Icc a b}) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ {x | x ∈ U ∧ f x = a} ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞ Φ
        (Ioo (-δ) (b-a+δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (0,y) = y) ∧
      (∀ y ∈ V, (∀ t ∈ Ioo (-δ) (b-a+δ), Φ (t,y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 (n + 1)) (fun t => Φ (t,y))
          (D.normalizedGradient f) (Ioo (-δ) (b-a+δ))) ∧
      ∀ c ∈ Icc a b,
        letI := openLevelSetChartedSpace hf U hreg n a
        letI := openLevelSetChartedSpace hf U hreg n c
        ∃ e : Diffeomorph (𝓡 n) (𝓡 n) (openLevelSet f U a) (openLevelSet f U c) ∞,
          ∀ x, openLevelIncl f U c (e x) = Φ (c-a, openLevelIncl f U a x) := by
  have hcompact (c : ℝ) (hc : c ∈ Icc a b) :
      IsCompact {x | x ∈ U ∧ f x = c} := by
    have hh := hband.inter_right (isClosed_eq hf.continuous continuous_const (f := f) (g := fun _ => c))
    convert hh using 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro hx
      exact ⟨⟨hx.1, hx.2 ▸ hc⟩, hx.2⟩
    · exact fun hx => ⟨hx.1.1, hx.2⟩
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  obtain ⟨V, δ, Φ, hV, hKV, hVU, hδ, hΦ, hinit, horbit, hlevel⟩ :=
    D.exists_normalizedGradient_flow_on_compact_regular_band hf U.isOpen hreg hband
      (hcompact a ha) (fun _ hx => hx.1) (sub_nonneg.mpr hab)
      (fun _ hx => hx.2.ge) (fun x hx => by rw [hx.2]; linarith)
  have hX := (D.contMDiffOn_normalizedGradient_of_regular U.isOpen hf.contMDiffOn hreg).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hneg : D.normalizedGradient (fun x => -f x) = fun x => -D.normalizedGradient f x :=
    funext (fun x => D.normalizedGradient_neg ((hf x).mdifferentiableAt (by simp)))
  refine ⟨V,δ,Φ,hV,hKV,hVU,hδ,hΦ,hinit,horbit,?_⟩
  intro c hc
  let := openLevelSetChartedSpace hf U hreg n a
  let := openLevelSetChartedSpace hf U hreg n c
  have hregneg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (fun y => -f y) x ≠ 0 := by
    intro x hx
    change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (-f) x ≠ 0
    rw [mfderiv_neg]
    exact neg_ne_zero.mpr (hreg x hx)
  have hbandneg : IsCompact {x | x ∈ U ∧ -f x ∈ Icc (-b) (-a)} := by
    convert hband using 1
    ext x
    simp only [mem_ofPred_eq, mem_Icc, neg_le_neg_iff]
    tauto
  obtain ⟨W, ε, Ψ, hW, hKW, hWU, hε, hΨ, hzeroΨ, hflowΨ, hlevelΨ⟩ :=
    D.exists_normalizedGradient_flow_on_compact_regular_band hf.neg U.isOpen hregneg hbandneg
      (hcompact c hc) (fun _ hx => hx.1) (sub_nonneg.mpr hc.1)
      (fun x hx => by rw [hx.2]; linarith [hc.2])
      (fun x hx => by rw [hx.2]; linarith)
  let s := c-a
  have hs : s ∈ Icc 0 (b-a) := ⟨sub_nonneg.mpr hc.1, sub_le_sub_right hc.2 a⟩
  have hsδ : s ∈ Ioo (-δ) (b-a+δ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hsε : s ∈ Ioo (-ε) (s+ε) := ⟨by linarith [hs.1],by linarith⟩
  have hxV (x : openLevelSet f U a) : openLevelIncl f U a x ∈ V := hKV ⟨x.1.2,x.2⟩
  have hyW (y : openLevelSet f U c) : openLevelIncl f U c y ∈ W := hKW ⟨y.1.2,y.2⟩
  have hfwd (x : openLevelSet f U a) :
      Φ (s,openLevelIncl f U a x) ∈ U ∧ f (Φ (s,openLevelIncl f U a x)) = c := by
    refine ⟨(horbit _ (hxV x)).1 s hsδ, ?_⟩
    rw [hlevel _ (hxV x) s hs, show f (openLevelIncl f U a x) = a from x.2]
    dsimp [s]
    ring
  have hbwd (y : openLevelSet f U c) :
      Ψ (s,openLevelIncl f U c y) ∈ U ∧ f (Ψ (s,openLevelIncl f U c y)) = a := by
    refine ⟨(hflowΨ _ (hyW y)).1 s hsε, ?_⟩
    have hh := hlevelΨ _ (hyW y) s ⟨hs.1,le_rfl⟩
    change -f (Ψ (s,openLevelIncl f U c y)) = -f (openLevelIncl f U c y) + s at hh
    rw [show f (openLevelIncl f U c y) = c from y.2] at hh
    dsimp [s] at hh
    linarith
  let F : openLevelSet f U a → openLevelSet f U c :=
    fun x => ⟨⟨Φ (s,openLevelIncl f U a x), (hfwd x).1⟩, (hfwd x).2⟩
  let G : openLevelSet f U c → openLevelSet f U a :=
    fun y => ⟨⟨Ψ (s,openLevelIncl f U c y), (hbwd y).1⟩, (hbwd y).2⟩
  have hshort : Ioo (-δ) (s+δ) ⊆ Ioo (-δ) (b-a+δ) :=
    Ioo_subset_Ioo le_rfl (by linarith [hs.2])
  have hGF : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hh := Poincare.Manifold.reverse_integralCurve_endpoint U.isOpen hX hs.1 hδ hε
      (fun t ht => (horbit _ (hxV x)).1 t (hshort ht))
      ((horbit _ (hxV x)).2.mono hshort)
      (by simpa only [hneg] using (hflowΨ _ (hyW (F x))).2)
      (by simpa only [F, openLevelIncl] using (hzeroΨ _ (hyW (F x))).symm)
    exact hh.trans (hinit _ (hxV x))
  have hFG : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hXneg : ContMDiffOn (𝓡 (n + 1)) ((𝓡 (n + 1)).prod (𝓡 (n + 1))) 1
        (T% (fun x => -D.normalizedGradient f x)) U := by
      intro x hx
      exact (hX x hx).neg_section
    have hh := Poincare.Manifold.reverse_integralCurve_endpoint U.isOpen hXneg hs.1 hε hδ
      (hflowΨ _ (hyW y)).1
      (by simpa only [hneg] using (hflowΨ _ (hyW y)).2)
      (by simpa only [neg_neg] using ((horbit _ (hxV (G y))).2.mono hshort))
      (by simpa only [G, openLevelIncl] using (hinit _ (hxV (G y))).symm)
    exact hh.trans (hzeroΨ _ (hyW y))
  have hFs : ContMDiff (𝓡 n) (𝓡 n) ∞ F := by
    intro x
    apply (contMDiffAt_into_openLevelSet_iff hf n c U hreg F x).mpr
    exact (hΦ.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hsδ,hxV x⟩)).comp x
      (contMDiffAt_const.prodMk (contMDiff_openLevelIncl hf U hreg n a x))
  have hGs : ContMDiff (𝓡 n) (𝓡 n) ∞ G := by
    intro y
    apply (contMDiffAt_into_openLevelSet_iff hf n a U hreg G y).mpr
    exact (hΨ.contMDiffAt ((isOpen_Ioo.prod hW).mem_nhds ⟨hsε,hyW y⟩)).comp y
      (contMDiffAt_const.prodMk (contMDiff_openLevelIncl hf U hreg n c y))
  exact ⟨{ toFun := F
           invFun := G
           left_inv := hGF
           right_inv := hFG
           contMDiff_toFun := hFs
           contMDiff_invFun := hGs }, fun _ => rfl⟩
end PoincareConjecture.LeviCivitaData
