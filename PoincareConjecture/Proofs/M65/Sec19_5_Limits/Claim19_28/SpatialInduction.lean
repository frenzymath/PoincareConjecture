import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateRecurrences
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations
import PoincareConjecture.Proofs.M07.Analysis.ODE.Linear.JetBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture

private def m65JetBound {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : ι → Set ℝ) (f : ι → ℝ → V) (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ S i → ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C

private theorem m65JetBound_all {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : ι → Set ℝ} {f : ι → ℝ → V} {m : ℕ}
    (h : ∀ j ≤ m, m65JetBound S f j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ i x, x ∈ S i →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C := by
  classical
  choose C hC hb using fun j : Fin (m + 1) => h j (by omega)
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j hj i x hx
  let q : Fin (m + 1) := ⟨j, by omega⟩
  exact (hb q i x hx).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ q))

private theorem m65JetBound_prod {ι V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : ι → Set ℝ} {f : ι → ℝ → V} {g : ι → ℝ → W} {m : ℕ}
    (hf : ∀ i x, x ∈ S i → ContDiffAt ℝ ∞ (f i) x)
    (hg : ∀ i x, x ∈ S i → ContDiffAt ℝ ∞ (g i) x)
    (hfb : m65JetBound S f m) (hgb : m65JetBound S g m) :
    m65JetBound S (fun i x => (f i x, g i x)) m := by
  obtain ⟨A, hA, ha⟩ := hfb
  obtain ⟨B, hB, hb⟩ := hgb
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro i x hx
  rw [iteratedFDeriv_prodMk (hf i x hx) (hg i x hx)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m), ContinuousMultilinearMap.opNorm_prod]
  exact max_le ((ha i x hx).trans (le_max_left _ _))
    ((hb i x hx).trans (le_max_right _ _))

private theorem m65JetBound_comp {ι V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : ι → Set ℝ} {f : ι → ℝ → V} {g : V → W} {K : Set V} {m : ℕ}
    (hK : IsCompact K) (hg : ∀ q ∈ K, ContDiffAt ℝ ∞ g q)
    (hf : ∀ i x, x ∈ S i → ContDiffAt ℝ ∞ (f i) x)
    (hrange : ∀ i, MapsTo (f i) (S i) K)
    (hbound : ∀ j ≤ m, m65JetBound S f j) :
    m65JetBound S (fun i => g ∘ f i) m := by
  classical
  have hout (j : Fin (m + 1)) : ∃ A : ℝ, ∀ q ∈ K,
      ‖iteratedFDeriv ℝ (j : ℕ) g q‖ ≤ A :=
    hK.exists_bound_of_continuousOn (fun q hq =>
      ((hg q hq).continuousAt_iteratedFDeriv
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).continuousWithinAt)
  choose A hA using hout
  let C : ℝ := ∑ j, max (A j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  obtain ⟨B, hB, hb⟩ := m65JetBound_all hbound
  refine ⟨m.factorial * C * (max B 1) ^ m, by positivity, ?_⟩
  intro i x hx
  apply Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_le_of_contDiffAt
    (hf i x hx) (hg _ (hrange i hx)) m
  · intro j hj
    let q : Fin (m + 1) := ⟨j, by omega⟩
    exact (hA q _ (hrange i hx)).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun l _ => le_max_right (A l) 0) (Finset.mem_univ q)))
  · intro j hj hjm
    exact (hb j hjm i x hx).trans ((le_max_left _ _).trans
      (le_self_pow₀ (le_max_right B 1) (Nat.ne_of_gt hj)))

private theorem m65JetBound_congr {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : ι → Set ℝ} {f g : ι → ℝ → V} {m : ℕ}
    (heq : ∀ i x, x ∈ S i → f i =ᶠ[𝓝 x] g i) (h : m65JetBound S f m) :
    m65JetBound S g m := by
  obtain ⟨B, hB, hb⟩ := h
  refine ⟨B, hB, ?_⟩
  intro i x hx
  rw [← ((heq i x hx).iteratedFDeriv ℝ m).eq_of_nhds]
  exact hb i x hx

private theorem m65JetBound_succ {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : ι → Set ℝ} {f g : ι → ℝ → V} {m : ℕ}
    (heq : ∀ i x, x ∈ S i → deriv (f i) =ᶠ[𝓝 x] g i)
    (h : m65JetBound S g m) : m65JetBound S f (m + 1) := by
  obtain ⟨B, hB, hb⟩ := m65JetBound_congr (fun i x hx => (heq i x hx).symm) h
  refine ⟨B, hB, ?_⟩
  intro i x hx
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ',
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hb i x hx

private theorem m65JetBound_mono {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S T : ι → Set ℝ} {f : ι → ℝ → V} {m : ℕ}
    (hST : ∀ i, S i ⊆ T i) (h : m65JetBound T f m) : m65JetBound S f m := by
  obtain ⟨B, hB, hb⟩ := h
  exact ⟨B, hB, fun i x hx => hb i x (hST i hx)⟩

private theorem m65JetBound_pi {ι η V : Type*} [Fintype η]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : ι → Set ℝ} {f : η → ι → ℝ → V} {m : ℕ}
    (hs : ∀ j i x, x ∈ S i → ContDiffAt ℝ ∞ (f j i) x)
    (hb : ∀ j, m65JetBound S (f j) m) :
    m65JetBound S (fun i x j => f j i x) m := by
  classical
  choose B hB hbound using hb
  let C := ∑ j, B j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hB j)
  refine ⟨C, hC, ?_⟩
  intro i x hx
  have hf : ContDiffAt ℝ ∞ (fun y j => f j i y) x :=
    contDiffAt_pi.mpr (fun j => hs j i x hx)
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have heq := congrArg (fun T => T v)
    ((ContinuousLinearMap.proj j).iteratedFDeriv_comp_left hf
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
  change iteratedFDeriv ℝ m (f j i) x v =
    (iteratedFDeriv ℝ m (fun y j => f j i y) x v) j at heq
  rw [← heq]
  exact ((iteratedFDeriv ℝ m (f j i) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((hbound j i x hx).trans
      (Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ j)))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

private theorem m65JetBound_cover {ι η V : Type*} [Finite η]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : η → ι → Set ℝ} {f : ι → ℝ → V} {m : ℕ}
    (hcover : ∀ i x, ∃ j, x ∈ S j i)
    (hb : ∀ j, m65JetBound (S j) f m) :
    m65JetBound (fun _ => univ) f m := by
  classical
  let := Fintype.ofFinite η
  choose B hB hbound using hb
  refine ⟨∑ j, B j, Finset.sum_nonneg (fun j _ => hB j), ?_⟩
  intro i x _
  obtain ⟨j, hj⟩ := hcover i x
  exact (hbound j i x hj).trans
    (Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ j))

private theorem m65JetBound_speedODE {κ : Type*} {a b r s : ℝ}
    (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    {v α : κ → ℝ × ℝ → ℝ} {v₀ : κ → ℝ} {B₀ : ℝ}
    (hB₀ : 0 ≤ B₀) (hv₀ : ∀ k, ‖v₀ k‖ ≤ B₀)
    (hv : ∀ k, ContDiffOn ℝ ∞ (v k) (Ioo a b ×ˢ univ))
    (hα : ∀ k, ContDiffOn ℝ ∞ (α k) (Ioo a b ×ˢ univ))
    (hode : ∀ k t x, t ∈ Ioo a b →
      HasDerivAt (fun u => v k (u, x)) (α k (t, x) * v k (t, x)) t)
    (hinit : ∀ k x, v k (r, x) = v₀ k) (m : ℕ)
    (hbound : ∀ j ≤ m, m65JetBound (fun _ : κ × Icc r s => univ)
      (fun k x => α k.1 (k.2, x)) j) :
    m65JetBound (fun _ : κ × Icc r s => univ) (fun k x => v k.1 (k.2, x)) m := by
  obtain ⟨C, hC, hb⟩ := m65JetBound_all hbound
  refine ⟨B₀ * Real.exp ((2 : ℝ) ^ m * C * (s - r)), by positivity, ?_⟩
  intro k x _
  let L := ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ
  let A : ℝ × ℝ → ℝ →L[ℝ] ℝ := fun z => L (α k.1 z)
  have hW : IsOpen (Ioo a b ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ univ) :=
    L.toContinuousLinearEquiv.contDiff.comp_contDiffOn (hα k.1)
  have hAode : ∀ z ∈ Ioo a b ×ˢ (univ : Set ℝ),
      Poincare.ODE.Parameter.timeFDeriv (v k.1) z = A z (v k.1 z) := by
    intro z hz
    rw [Poincare.ODE.Parameter.timeFDeriv_eq_slice
      (((hv k.1).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)),
      (hode k.1 z.1 z.2 hz.1).deriv]
    simp only [A, L, ContinuousLinearMap.toSpanSingletonLIE_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  have hAbound (j : ℕ) (hj : j ≤ m) (t : ℝ) (ht : t ∈ Icc r s) (y : ℝ)
      (_hy : y ∈ (univ : Set ℝ)) :
      ‖iteratedFDeriv ℝ j (fun u => A (t, u)) y‖ ≤ C := by
    change ‖iteratedFDeriv ℝ j (L ∘ fun u => α k.1 (t, u)) y‖ ≤ C
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hb j hj (k.1, ⟨t, ht⟩) y (mem_univ y)
  have h := Poincare.ODE.Linear.norm_iteratedFDeriv_linearODE_le m hrs hC
    isOpen_univ hW (fun z hz => ⟨hsub hz.1, hz.2⟩) hA (hv k.1) hAode
    (fun y _ => hinit k.1 y) hAbound k.2.property (mem_univ x)
  refine h.trans (mul_le_mul (hv₀ k.1) ?_ (Real.exp_nonneg _) hB₀)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right k.2.property.2 r) (by positivity)

theorem m65UniformSpatialJets_of_triangularRecurrences
    {κ ι V : Type*} [Finite ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b r s : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    (v α : κ → ℝ × ℝ → ℝ) (v₀ : κ → ℝ)
    (S : ι → κ × Icc r s → Set ℝ)
    (f : ι → ℕ → κ × Icc r s → ℝ → V)
    (R : ι → ∀ j : ℕ, (ℝ × (Fin (j + 2) → V)) → V)
    (A : ι → (Fin 3 → V) → ℝ)
    (ΩR : ι → ∀ j : ℕ, Set (ℝ × (Fin (j + 2) → V)))
    (ΩA : ι → Set (Fin 3 → V))
    (hΩR : ∀ i j, IsOpen (ΩR i j)) (hΩA : ∀ i, IsOpen (ΩA i))
    (hR : ∀ i j, ContDiffOn ℝ ∞ (R i j) (ΩR i j))
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (ΩA i))
    (hRcompact : ∀ i j, ∃ K : Set (ℝ × (Fin (j + 2) → V)), IsCompact K ∧
      K ⊆ ΩR i j ∧ ∀ k x, x ∈ S i k →
        (v k.1 (k.2, x), fun l : Fin (j + 2) => f i l k x) ∈ K)
    (hAcompact : ∀ i, ∃ K : Set (Fin 3 → V), IsCompact K ∧ K ⊆ ΩA i ∧
      ∀ k x, x ∈ S i k → (fun l : Fin 3 => f i l k x) ∈ K)
    (hcover : ∀ k x, ∃ i, x ∈ S i k)
    (hv : ∀ k, ContDiffOn ℝ ∞ (v k) (Ioo a b ×ˢ univ))
    (hα : ∀ k, ContDiffOn ℝ ∞ (α k) (Ioo a b ×ˢ univ))
    (hf : ∀ i j k x, x ∈ S i k → ContDiffAt ℝ ∞ (f i j k) x)
    (hode : ∀ k t x, t ∈ Ioo a b →
      HasDerivAt (fun u => v k (u, x)) (α k (t, x) * v k (t, x)) t)
    (hinit : ∀ k x, v k (r, x) = v₀ k)
    (hvzero : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : κ × Icc r s, ∀ x, |v k.1 (k.2, x)| ≤ B)
    (hfzero : ∀ i j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k x, x ∈ S i k → ‖f i j k x‖ ≤ B)
    (hrec : ∀ i j k x, x ∈ S i k → deriv (f i j k) =ᶠ[𝓝 x]
      fun y => R i j (v k.1 (k.2, y), fun l : Fin (j + 2) => f i l k y))
    (hαeq : ∀ i k x, x ∈ S i k → (fun y => α k.1 (k.2, y)) =ᶠ[𝓝 x]
      fun y => A i (fun l : Fin 3 => f i l k y)) :
    ∀ m : ℕ,
      (∃ B : ℝ, 0 ≤ B ∧ ∀ k : κ × Icc r s, ∀ x,
        ‖iteratedFDeriv ℝ m (fun y => v k.1 (k.2, y)) x‖ ≤ B) ∧
      ∀ i j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k x, x ∈ S i k →
        ‖iteratedFDeriv ℝ m (f i j k) x‖ ≤ B := by
  obtain ⟨B₀, hB₀, hvB₀⟩ := hvzero
  have hv₀ (k : κ) : ‖v₀ k‖ ≤ B₀ := by
    rw [← hinit k 0, Real.norm_eq_abs]
    exact hvB₀ (k, ⟨r, left_mem_Icc.mpr hrs⟩) 0
  have hvs (k : κ × Icc r s) (x : ℝ) :
      ContDiffAt ℝ ∞ (fun y => v k.1 (k.2, y)) x :=
    ((hv k.1).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hsub k.2.property, mem_univ x⟩)).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hmain : ∀ m : ℕ,
      m65JetBound (fun _ : κ × Icc r s => univ) (fun k x => v k.1 (k.2, x)) m ∧
      ∀ i j, m65JetBound (S i) (f i j) m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero =>
        constructor
        · exact ⟨B₀, hB₀, fun k x _ => by
            simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hvB₀ k x⟩
        · intro i j
          simpa only [m65JetBound, norm_iteratedFDeriv_zero] using hfzero i j
      | succ m =>
        have hvprev (l : ℕ) (hl : l ≤ m) :
            m65JetBound (fun _ : κ × Icc r s => univ) (fun k x => v k.1 (k.2, x)) l :=
          (ih l (Nat.lt_succ_of_le hl)).1
        have hfprev (i : ι) (j l : ℕ) (hl : l ≤ m) : m65JetBound (S i) (f i j) l :=
          (ih l (Nat.lt_succ_of_le hl)).2 i j
        have hfnext (i : ι) (j : ℕ) : m65JetBound (S i) (f i j) (m + 1) := by
          apply m65JetBound_succ (hrec i j)
          obtain ⟨K, hK, hKΩ, hKrange⟩ := hRcompact i j
          apply m65JetBound_comp hK
            (fun z hz => (hR i j).contDiffAt ((hΩR i j).mem_nhds (hKΩ hz)))
            (fun k x hx => (hvs k x).prodMk
              (contDiffAt_pi.mpr (fun l => hf i l k x hx))) hKrange
          intro l hl
          exact m65JetBound_prod (fun k x _ => hvs k x)
            (fun k x hx => contDiffAt_pi.mpr (fun q => hf i q k x hx))
            (m65JetBound_mono (fun _ => subset_univ _) (hvprev l hl))
            (m65JetBound_pi (fun q k x hx => hf i q k x hx)
              (fun q => hfprev i q l hl))
        have hffield (i : ι) (j l : ℕ) (hl : l ≤ m + 1) :
            m65JetBound (S i) (f i j) l := by
          by_cases hlm : l ≤ m
          · exact hfprev i j l hlm
          · have heq : l = m + 1 := by omega
            subst l
            exact hfnext i j
        have hαbound (l : ℕ) (hl : l ≤ m + 1) :
            m65JetBound (fun _ : κ × Icc r s => univ) (fun k x => α k.1 (k.2, x)) l := by
          apply m65JetBound_cover hcover
          intro i
          apply m65JetBound_congr (fun k x hx => (hαeq i k x hx).symm)
          obtain ⟨K, hK, hKΩ, hKrange⟩ := hAcompact i
          apply m65JetBound_comp hK
            (fun z hz => (hA i).contDiffAt ((hΩA i).mem_nhds (hKΩ hz)))
            (fun k x hx => contDiffAt_pi.mpr (fun q => hf i q k x hx)) hKrange
          intro j hj
          exact m65JetBound_pi (fun q k x hx => hf i q k x hx)
            (fun q => hffield i q j (hj.trans hl))
        exact ⟨m65JetBound_speedODE hrs hsub hB₀ hv₀ hv hα hode hinit (m + 1) hαbound,
          hfnext⟩
  intro m
  obtain ⟨hvjet, hfjet⟩ := hmain m
  obtain ⟨B, hB, hb⟩ := hvjet
  exact ⟨⟨B, hB, fun k x => hb k x (mem_univ x)⟩, hfjet⟩

end PoincareConjecture
