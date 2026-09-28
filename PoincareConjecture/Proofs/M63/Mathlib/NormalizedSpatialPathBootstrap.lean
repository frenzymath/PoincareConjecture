import PoincareConjecture.Proofs.M63.Mathlib.ClosedTimeOpenStateSubstitution
import PoincareConjecture.Proofs.M63.Mathlib.CompactPathComposition
import PoincareConjecture.Proofs.M63.Mathlib.CompactPathDerivative
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open Set PoincareConjecture.M63
open scoped Topology ContDiff intervalIntegral

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {tau s : ℝ}

theorem exists_contDiff_pathFamily_of_normalized_spatial_recurrences
    (hts : tau < s) {U : Set E} (hU : IsOpen U)
    (A : (ℝ × E) × (E × E) → ℝ) (B : (ℝ × E) × (E × E) → E)
    (hA : ContDiffOn ℝ ∞ A ((Icc tau s ×ˢ U) ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B ((Icc tau s ×ˢ U) ×ˢ univ))
    (q : ℝ → ℝ → E) (v : ℝ → ℝ → ℝ) (r : ℕ → ℝ → ℝ → E) (v0 : ℝ)
    (hq : ContinuousOn (fun z : ℝ × ℝ => q z.1 z.2) (univ ×ˢ Icc tau s))
    (hr : ∀ i, ContinuousOn (fun z : ℝ × ℝ => r i z.1 z.2) (univ ×ˢ Icc tau s))
    (hguard : ∀ x, ∀ t ∈ Icc tau s, q x t ∈ U)
    (hv : ∀ x, ∀ t ∈ Icc tau s, v x t = v0 * Real.exp
      (-∫ u in tau..t, A ((u, q x u), (r 0 x u, r 1 x u))))
    (hqder : ∀ t ∈ Icc tau s, ∀ x,
      HasDerivAt (fun y => q y t) (v x t • r 0 x t) x)
    (hrder : ∀ i, ∀ t ∈ Icc tau s, ∀ x, HasDerivAt (fun y => r i y t)
      (v x t • (B ((t, q x t), (r 0 x t, r i x t)) + r (i + 1) x t)) x) :
    ∃ (Q : ℝ → C(Icc tau s, E)) (V : ℝ → C(Icc tau s, ℝ))
      (R : ℕ → ℝ → C(Icc tau s, E)),
      (∀ x (t : Icc tau s), Q x t = q x t) ∧
      (∀ x (t : Icc tau s), V x t = v x t) ∧
      (∀ i x (t : Icc tau s), R i x t = r i x t) ∧
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ V ∧ ∀ i, ContDiff ℝ ∞ (R i) := by
  let C := Icc tau s
  let Q : ℝ → C(C, E) := fun x => ⟨fun t => q x t,
    hq.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun t => ⟨mem_univ _, t.property⟩)⟩
  let R : ℕ → ℝ → C(C, E) := fun i x => ⟨fun t => r i x t,
    (hr i).comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun t => ⟨mem_univ _, t.property⟩)⟩
  have hQc : Continuous Q := ContinuousMap.continuous_of_continuous_uncurry Q
    (hq.comp_continuous (f := fun z : ℝ × C => (z.1, z.2.val))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨mem_univ _, z.2.property⟩))
  have hRc (i : ℕ) : Continuous (R i) := ContinuousMap.continuous_of_continuous_uncurry (R i)
    ((hr i).comp_continuous (f := fun z : ℝ × C => (z.1, z.2.val))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨mem_univ _, z.2.property⟩))
  let O : Set (E × (E × E)) := U ×ˢ univ
  let A' : ℝ × (E × (E × E)) → ℝ := fun z => A ((z.1, z.2.1), z.2.2)
  let B' : ℝ × (E × (E × E)) → E := fun z => B ((z.1, z.2.1), z.2.2)
  have hpair : ContDiff ℝ ∞
      (fun z : ℝ × (E × (E × E)) => ((z.1, z.2.1), z.2.2)) := by fun_prop
  have hA' : ContDiffOn ℝ ∞ A' (C ×ˢ O) :=
    hA.comp hpair.contDiffOn (fun z hz => ⟨⟨hz.1, hz.2.1⟩, mem_univ _⟩)
  have hB' : ContDiffOn ℝ ∞ B' (C ×ˢ O) :=
    hB.comp hpair.contDiffOn (fun z hz => ⟨⟨hz.1, hz.2.1⟩, mem_univ _⟩)
  obtain ⟨PhiA, hPhiA, hPhiAval⟩ := exists_contDiffOn_closedTime_pathSubstitution
    (uniqueDiffOn_Icc hts) (hU.prod isOpen_univ) A' hA'
  obtain ⟨PhiB, hPhiB, hPhiBval⟩ := exists_contDiffOn_closedTime_pathSubstitution
    (uniqueDiffOn_Icc hts) (hU.prod isOpen_univ) B' hB'
  let Lq : E →L[ℝ] E × (E × E) := ContinuousLinearMap.inl ℝ E (E × E)
  let Lp : E →L[ℝ] E × (E × E) :=
    (ContinuousLinearMap.inr ℝ E (E × E)).comp (ContinuousLinearMap.inl ℝ E E)
  let Lh : E →L[ℝ] E × (E × E) :=
    (ContinuousLinearMap.inr ℝ E (E × E)).comp (ContinuousLinearMap.inr ℝ E E)
  let J : ℕ → ℝ → C(C, E × (E × E)) := fun i x =>
    Lq.compLeftContinuous ℝ C (Q x) + Lp.compLeftContinuous ℝ C (R 0 x) +
      Lh.compLeftContinuous ℝ C (R i x)
  have hJval (i : ℕ) (x : ℝ) (t : C) :
      J i x t = (q x t, (r 0 x t, r i x t)) := by
    change ((q x t, (0, 0)) : E × (E × E)) +
      ((0, (r 0 x t, 0)) : E × (E × E)) +
      ((0, (0, r i x t)) : E × (E × E)) = _
    simp only [Prod.mk_add_mk, zero_add, add_zero]
  have hJguard (i : ℕ) (x : ℝ) : range (J i x) ⊆ O := by
    rintro z ⟨t, rfl⟩
    rw [hJval]
    exact ⟨hguard x t t.property, mem_univ _⟩
  let aPath : ℝ → C(C, ℝ) := fun x => PhiA (J 1 x)
  let bPath : ℕ → ℝ → C(C, E) := fun i x => PhiB (J i x)
  have haVal (x : ℝ) (t : C) :
      aPath x t = A ((t.val, q x t), (r 0 x t, r 1 x t)) := by
    rw [hPhiAval (J 1 x) (hJguard 1 x) t]
    change A ((t.val, (J 1 x t).1), (J 1 x t).2) = _
    rw [hJval]
  have hbVal (i : ℕ) (x : ℝ) (t : C) :
      bPath i x t = B ((t.val, q x t), (r 0 x t, r i x t)) := by
    rw [hPhiBval (J i x) (hJguard i x) t]
    change B ((t.val, (J i x t).1), (J i x t).2) = _
    rw [hJval]
  let P : C(C, ℝ) →L[ℝ] C(C, ℝ) :=
    PoincareConjecture.M14.closedPathPrimitive ⟨tau, le_rfl, hts.le⟩
  let eExp : C(ℝ, ℝ) := ⟨Real.exp, Real.continuous_exp⟩
  let V : ℝ → C(C, ℝ) := fun x => v0 • eExp.comp (-P (aPath x))
  have hExp : ContDiff ℝ ∞ (fun f : C(C, ℝ) => eExp.comp f) :=
    contDiff_postcomp_independent_universes C eExp Real.contDiff_exp
  have hVval (x : ℝ) (t : C) : V x t = v x t := by
    have hInt : P (aPath x) t =
        ∫ u in tau..t.val, A ((u, q x u), (r 0 x u, r 1 x u)) := by
      rw [PoincareConjecture.M14.closedPathPrimitive_apply]
      apply intervalIntegral.integral_congr
      intro u hu
      have hut : u ∈ Icc tau t.val := by simpa only [uIcc_of_le t.property.1] using hu
      have huC : u ∈ Icc tau s := ⟨hut.1, hut.2.trans t.property.2⟩
      change aPath x (projIcc tau s hts.le u) = A ((u, q x u), (r 0 x u, r 1 x u))
      rw [projIcc_of_mem _ huC]
      exact haVal x ⟨u, huC⟩
    change v0 * Real.exp (-P (aPath x) t) = v x t
    rw [hInt, hv x t t.property]
  let scalarAction : C(ℝ × E, E) :=
    ⟨fun z => z.1 • z.2, continuous_fst.smul continuous_snd⟩
  have hAction : ContDiff ℝ ∞
      (fun f : C(C, ℝ × E) => scalarAction.comp f) :=
    contDiff_postcomp_independent_universes C scalarAction (contDiff_fst.smul contDiff_snd)
  let SMul : C(C, ℝ) → C(C, E) → C(C, E) := fun f g =>
    ⟨fun t => f t • g t, f.continuous.smul g.continuous⟩
  have hSMul {k : ℕ∞} {f : ℝ → C(C, ℝ)} {g : ℝ → C(C, E)}
      (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
      ContDiff ℝ k (fun x => SMul (f x) (g x)) := by
    have hk : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : k ≤ ⊤)
    have hp := ((ContinuousLinearMap.inl ℝ ℝ E).compLeftContinuous ℝ C).contDiff.comp hf
    have hq' := ((ContinuousLinearMap.inr ℝ ℝ E).compLeftContinuous ℝ C).contDiff.comp hg
    convert (hAction.of_le hk).comp (hp.add hq') using 1
    funext x
    apply ContinuousMap.ext
    intro t
    change f x t • g x t = ((f x t, (0 : E)) + (0, g x t)).1 •
      ((f x t, (0 : E)) + (0, g x t)).2
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hregular (k : ℕ∞) (hQ : ContDiff ℝ k Q)
      (hR : ∀ i, ContDiff ℝ k (R i)) :
      ContDiff ℝ k V ∧ ∀ i, ContDiff ℝ k (bPath i) := by
    have hk : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : k ≤ ⊤)
    have hJ (i : ℕ) : ContDiff ℝ k (J i) :=
      (((Lq.compLeftContinuous ℝ C).contDiff.comp hQ).add
        ((Lp.compLeftContinuous ℝ C).contDiff.comp (hR 0))).add
          ((Lh.compLeftContinuous ℝ C).contDiff.comp (hR i))
    have ha : ContDiff ℝ k aPath :=
      (hPhiA.of_le hk).comp_contDiff (hJ 1) (hJguard 1)
    have hb (i : ℕ) : ContDiff ℝ k (bPath i) :=
      (hPhiB.of_le hk).comp_contDiff (hJ i) (hJguard i)
    exact ⟨((hExp.of_le hk).comp ((P.contDiff.comp ha).neg)).const_smul v0, hb⟩
  have upgrade (m : ℕ) {f df : ℝ → C(C, E)} (hdf : ContDiff ℝ m df)
      (hd : ∀ x, HasDerivAt f (df x) x) : ContDiff ℝ (m + 1) f := by
    refine contDiff_succ_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
    have heq : deriv f = df := funext fun x => (hd x).deriv
    rwa [heq]
  have hfinite : ∀ m : ℕ, ContDiff ℝ m Q ∧ ∀ i, ContDiff ℝ m (R i) := by
    intro m
    induction m with
    | zero => exact ⟨contDiff_zero.mpr hQc, fun i => contDiff_zero.mpr (hRc i)⟩
    | succ m ih =>
      have hreg := hregular (m : ℕ∞) ih.1 ih.2
      let Dq : ℝ → C(C, E) := fun x => SMul (V x) (R 0 x)
      let Dr : ℕ → ℝ → C(C, E) := fun i x =>
        SMul (V x) (bPath i x + R (i + 1) x)
      have hDq : ContDiff ℝ m Dq := hSMul hreg.1 (ih.2 0)
      have hDr (i : ℕ) : ContDiff ℝ m (Dr i) :=
        hSMul hreg.1 ((hreg.2 i).add (ih.2 (i + 1)))
      have hqd (x : ℝ) : HasDerivAt Q (Dq x) x := by
        apply hasDerivAt_compact_curry isOpen_univ Q Dq (mem_univ x) hDq.continuous.continuousAt
        intro y _hy t
        change HasDerivAt (fun z => q z t.val) (V y t • r 0 y t.val) y
        rw [hVval]
        exact hqder t t.property y
      have hrd (i : ℕ) (x : ℝ) : HasDerivAt (R i) (Dr i x) x := by
        apply hasDerivAt_compact_curry isOpen_univ (R i) (Dr i) (mem_univ x)
          (hDr i).continuous.continuousAt
        intro y _hy t
        change HasDerivAt (fun z => r i z t.val)
          (V y t • (bPath i y t + r (i + 1) y t.val)) y
        rw [hVval, hbVal]
        exact hrder i t t.property y
      exact ⟨upgrade m hDq hqd, fun i => upgrade m (hDr i) (hrd i)⟩
  have hQ : ContDiff ℝ ∞ Q := contDiff_infty.mpr fun m => (hfinite m).1
  have hR (i : ℕ) : ContDiff ℝ ∞ (R i) := contDiff_infty.mpr fun m => (hfinite m).2 i
  exact ⟨Q, V, R, fun _ _ => rfl, hVval, fun _ _ _ => rfl,
    hQ, (hregular ⊤ hQ hR).1, hR⟩
