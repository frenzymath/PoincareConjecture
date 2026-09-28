import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.ScalarGraph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

private theorem vertical_mfderiv_bijective_at (h : RoundCylinderSpace → ℝ)
    (p : RoundCylinderSpace)
    (hh : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h p)
    {a : ℝ} (ha : a ≠ 0)
    (hderiv : HasDerivAt (fun t => h (p.1, t)) a p.2) :
    Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) p) := by
  let D : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] ℝ :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) h p
  let Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q => h (q, p.2)) p.1
  have hvertical (v : EuclideanSpace ℝ (Fin 2) × ℝ) :
      D v = Q v.1 + a * v.2 := by
    dsimp only [D, Q]
    erw [mfderiv_prod_eq_add_apply (hh.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, fderiv_eq_deriv_mul (𝕜 := ℝ), hderiv.deriv]
    rfl
  have htotal : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun z => (z.1, h z)) p =
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).prod D := by
    rw [mfderiv_prodMk mdifferentiableAt_fst (hh.mdifferentiableAt (by simp)),
      mfderiv_fst]
    rfl
  have hinj : Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) p) := by
    intro v w hvw
    rw [htotal] at hvw
    have hfirst := congrArg Prod.fst hvw
    change v.1 = w.1 at hfirst
    have hsecond : D v = D w := congrArg Prod.snd hvw
    rw [hvertical, hvertical, hfirst] at hsecond
    exact Prod.ext hfirst (mul_left_cancel₀ ha (add_left_cancel hsecond))
  let L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun z : RoundCylinderSpace => (z.1, h z)) p
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩

private theorem injOn_of_abs_deriv_ge {F : ℝ → ℝ} {W m : ℝ} (hm : 0 < m)
    (hF : ∀ t ∈ Icc (-W) W, ContDiffAt ℝ ∞ F t)
    (hd : ∀ t ∈ Icc (-W) W, m ≤ |deriv F t|) : InjOn F (Ioo (-W) W) := by
  have hlt {s t : ℝ} (hs : s ∈ Ioo (-W) W) (ht : t ∈ Ioo (-W) W)
      (hst : s < t) (heq : F s = F t) : False := by
    have hc : ContinuousOn F (Icc s t) := fun x hx =>
      (hF x ⟨hs.1.le.trans hx.1, hx.2.trans ht.2.le⟩).continuousAt.continuousWithinAt
    obtain ⟨x, hx, hzero⟩ := exists_deriv_eq_zero hst hc heq
    have hb := hd x ⟨hs.1.le.trans hx.1.le, hx.2.le.trans ht.2.le⟩
    rw [hzero, abs_zero] at hb
    exact (not_le_of_gt hm) hb
  intro s hs t ht heq
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim (hlt hs ht h heq)
  · exact h
  · exact False.elim (hlt ht hs h heq.symm)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_smooth_cylinderCover_level_graph
    (Φ : RoundCylinderSpace → M) {s : ℝ}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-s) s))
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    {W m c : ℝ} (hW : 0 < W) (hWs : W < s) (hm : 0 < m)
    (hd : ∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (-W) W →
      m ≤ |deriv (fun a : ℝ => f (Φ (q, a))) t|)
    (hcenter : ∀ q : UnitTwoSphere, |f (Φ (q, 0)) - c| < m * W) :
    ∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ q, h q ∈ Ioo (-W) W) ∧
      (∀ q, f (Φ (q, h q)) = c) ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q => Φ (q, h q)) ∧
      {x | x ∈ Φ '' (univ ×ˢ Ioo (-W) W) ∧ f x = c} =
        range (fun q => Φ (q, h q)) ∧
      (∀ q t, t ∈ Ioo (-W) W → f (Φ (q, t)) = c → t = h q) := by
  let S : Set RoundCylinderSpace := univ ×ˢ Ioo (-W) W
  let H : RoundCylinderSpace → ℝ := f ∘ Φ
  let T : RoundCylinderSpace → RoundCylinderSpace := fun z => (z.1, H z)
  have hopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hdom {q : UnitTwoSphere} {t : ℝ} (ht : t ∈ Icc (-W) W) :
      (q, t) ∈ univ ×ˢ Ioo (-s) s :=
    ⟨mem_univ _, (neg_lt_neg hWs).trans_le ht.1, ht.2.trans_lt hWs⟩
  have hHs (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (-W) W) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (q, t) :=
    (hf _).comp (q, t) (hΦ.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds (hdom ht)))
  have hF (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (-W) W) :
      ContDiffAt ℝ ∞ (fun a : ℝ => f (Φ (q, a))) t := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (hHs q t ht).comp t (contMDiffAt_const.prodMk contMDiffAt_id)
  have hroot (q : UnitTwoSphere) :
      ∃! t : ℝ, t ∈ Ioo (-W) W ∧ f (Φ (q, t)) = c :=
    Poincare.Analysis.existsUnique_level_of_abs_deriv_ge hW hm
      (hF q) (hd q) (hcenter q)
  choose h hhroot hhunique using hroot
  have hTin : InjOn T S := by
    rintro ⟨q, a⟩ ha ⟨p, b⟩ hb heq
    have hq : q = p := congrArg Prod.fst heq
    subst p
    exact Prod.ext rfl (injOn_of_abs_deriv_ge hm (hF q) (hd q)
      ha.2 hb.2 (congrArg Prod.snd heq))
  let J := invFunOn T S
  have hleft : LeftInvOn J T S := hTin.leftInvOn_invFunOn
  have hinv (q : UnitTwoSphere) : J (q, c) = (q, h q) := by
    rw [show (q, c) = T (q, h q) from Prod.ext rfl (hhroot q).2.symm]
    exact hleft ⟨mem_univ _, (hhroot q).1⟩
  have hJs (q : UnitTwoSphere) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ J (q, c) := by
    have hp := (hhroot q).1
    have ht := hHs q (h q) ⟨hp.1.le, hp.2.le⟩
    have hax : deriv (fun t => H (q, t)) (h q) ≠ 0 := by
      intro hz
      have hb := hd q (h q) ⟨hp.1.le, hp.2.le⟩
      change m ≤ |deriv (fun t => H (q, t)) (h q)| at hb
      rw [hz, abs_zero] at hb
      exact (not_le_of_gt hm) hb
    have hder : HasDerivAt (fun t => H (q, t))
        (deriv (fun t => H (q, t)) (h q)) (h q) :=
      ((hF q (h q) ⟨hp.1.le, hp.2.le⟩).differentiableAt (by simp)).hasDerivAt
    have ht' := contMDiffAt_fst.prodMk ht
    have hd' := vertical_mfderiv_bijective_at H (q, h q) ht hax hder
    have hl : ∀ᶠ z in 𝓝 (q, h q), J (T z) = z :=
      Filter.Eventually.mono (hopen.mem_nhds (show (q, h q) ∈ S from ⟨mem_univ _, hp⟩))
        (fun _ hz => hleft hz)
    let : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) RoundCylinderSpace :=
      prodChartedSpace _ _ _ _
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ RoundCylinderSpace := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) UnitTwoSphere ℝ
    have heq : T (q, h q) = (q, c) := Prod.ext rfl (hhroot q).2
    rw [← modelWithCornersSelf_prod] at ht' hd' ⊢
    rw [← heq]
    exact Poincare.Geometry.Manifold.contMDiffAt_of_local_left_inverse_modelSpaces ht' hd' hl
  have hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h := by
    have heq : h = fun q => (J (q, c)).2 := funext (fun q => (congrArg Prod.snd (hinv q)).symm)
    rw [heq]
    intro q
    exact contMDiffAt_snd.comp q ((hJs q).comp q (contMDiffAt_id.prodMk contMDiffAt_const))
  refine ⟨h, hsmooth, fun q => (hhroot q).1, fun q => (hhroot q).2, ?_, ?_, ?_⟩
  · intro q
    exact (hΦ.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (hdom ⟨(hhroot q).1.1.le, (hhroot q).1.2.le⟩))).comp q
        (contMDiffAt_id.prodMk (hsmooth q))
  · ext x
    constructor
    · rintro ⟨⟨⟨q, t⟩, ht, rfl⟩, hc⟩
      exact ⟨q, congrArg (fun t => Φ (q, t)) (hhunique q t ⟨ht.2, hc⟩).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⟨(q, h q), ⟨mem_univ _, (hhroot q).1⟩, rfl⟩, (hhroot q).2⟩
  · intro q t ht hc
    exact hhunique q t ⟨ht, hc⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  in

theorem cylinderCover_level_height_even
    (Φ : RoundCylinderSpace → M) {f : M → ℝ} {h : UnitTwoSphere → ℝ} {W c : ℝ}
    (hdom : ∀ q, h q ∈ Ioo (-W) W)
    (hlevel : ∀ q, f (Φ (q, h q)) = c)
    (hunique : ∀ q t, t ∈ Ioo (-W) W → f (Φ (q, t)) = c → t = h q)
    (hanti : ∀ q t, t ∈ Ioo (-W) W → Φ (-q, t) = Φ (q, t)) :
    ∀ q, h (-q) = h q := by
  intro q
  exact (hunique (-q) (h q) (hdom q) (by rw [hanti q _ (hdom q), hlevel q])).symm

end PoincareConjecture
