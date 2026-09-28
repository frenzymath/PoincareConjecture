import PoincareConjecture.Proofs.M03.Existence.CompactTimeDependentFlowNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckCompatibleJetNative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Data.List.FinRange








set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Bundle

namespace PoincareConjecture.DeTurckSpatialParameterNative

open CompactTimeDependentFlowNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n

theorem exists_signed_diffeomorph_family
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    ∃ T : ℝ, 0 < T ∧ ∃ Phi : ℝ → Diffeomorph I I M M ∞,
      Phi 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t ∈ Ioo (-T) T, Phi (-t) = (Phi t).symm) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Phi q.1 q.2) (Ioo (-T) T ×ˢ univ) ∧
      ∀ t ∈ Ioo (-T) T, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Phi s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Phi t x))) := by
  classical
  obtain ⟨U, _, hU, eps, heps, alpha, hzero, hcurve, hsmooth⟩ :=
    exists_smooth_local_flow_on_compact V hV (isCompact_univ : IsCompact (univ : Set M))
  have hall (x : M) : x ∈ U := hU (mem_univ x)
  let T : ℝ := eps / 2
  have hT : 0 < T := by dsimp only [T]; positivity
  have hfull : Ioo (-T) T ⊆ Ioo (-eps) eps :=
    Ioo_subset_Ioo (by dsimp only [T]; linarith) (by dsimp only [T]; linarith)
  have hneg {t : ℝ} (ht : t ∈ Ioo (-T) T) : -t ∈ Ioo (-T) T :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hV1 : ContMDiff I ((𝓡 n).prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) := hV.of_le (by simp)
  have hfixed (t : ℝ) (ht : t ∈ Ioo (-eps) eps) :
      ContMDiff I I ∞ (fun x => alpha (x, t)) := by
    rw [← contMDiffOn_univ]
    exact hsmooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun x _ => ⟨hall x, ht⟩)
  let family (t : ℝ) (ht : t ∈ Ioo (-T) T) : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := fun x => alpha (x, t)
          invFun := fun x => alpha (x, -t)
          left_inv := fun x => local_flow_reverse hV1 heps hzero hcurve
            (hall x) ht (hall _)
          right_inv := fun x => by
            simpa only [neg_neg] using
              local_flow_reverse hV1 heps hzero hcurve (hall x) (hneg ht) (hall _) }
      contMDiff_toFun := hfixed t (hfull ht)
      contMDiff_invFun := hfixed (-t) (hfull (hneg ht)) }
  let Phi : ℝ → Diffeomorph I I M M ∞ := fun t =>
    if ht : t ∈ Ioo (-T) T then family t ht else Diffeomorph.refl I M ∞
  have hPhi (t : ℝ) (ht : t ∈ Ioo (-T) T) (x : M) : Phi t x = alpha (x, t) := by
    simp only [Phi, dif_pos ht]
    rfl
  have hPhiInv (t : ℝ) (ht : t ∈ Ioo (-T) T) (x : M) :
      (Phi t).symm x = alpha (x, -t) := by
    simp only [Phi, dif_pos ht]
    rfl
  refine ⟨T, hT, Phi, ?_, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    rw [hPhi 0 ⟨neg_lt_zero.mpr hT, hT⟩]
    exact hzero x (hall x)
  · intro t ht
    apply Diffeomorph.ext
    intro x
    rw [hPhi (-t) (hneg ht), hPhiInv t ht]
  · have hsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => alpha (q.2, q.1)) (Ioo (-T) T ×ˢ univ) :=
      hsmooth.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn
        (fun q hq => ⟨hall q.2, hfull hq.1⟩)
    exact hsm.congr (fun q hq => hPhi q.1 hq.1 q.2)
  · intro t ht x
    have htf := hfull ht
    have hd := ((hcurve x (hall x)) t htf).hasMFDerivAt
      (Ioo_mem_nhds htf.1 htf.2)
    have heq : (fun s => Phi s x) =ᶠ[𝓝 t] (fun s => alpha (x, s)) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hPhi s hs x)
    dsimp only at hd
    rw [← hPhi t ht x] at hd
    exact hd.congr_of_eventuallyEq heq

section FiniteComposition

variable {iota : Type*} [Fintype iota]


def composeFamily (Phi : iota → ℝ → Diffeomorph I I M M ∞) :
    List iota → (iota → ℝ) → Diffeomorph I I M M ∞
  | [], _ => Diffeomorph.refl I M ∞
  | i :: is, p => (Phi i (p i)).trans (composeFamily Phi is p)

theorem composeFamily_zero (Phi : iota → ℝ → Diffeomorph I I M M ∞)
    (hzero : ∀ i, Phi i 0 = Diffeomorph.refl I M ∞) (is : List iota) :
    composeFamily Phi is 0 = Diffeomorph.refl I M ∞ := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [composeFamily, Pi.zero_apply, hzero, ih, Diffeomorph.refl_trans]

theorem composeFamily_single_of_not_mem [DecidableEq iota]
    (Phi : iota → ℝ → Diffeomorph I I M M ∞)
    (hzero : ∀ i, Phi i 0 = Diffeomorph.refl I M ∞)
    (is : List iota) (i : iota) (hi : i ∉ is) (t : ℝ) :
    composeFamily Phi is (Pi.single i t) = Diffeomorph.refl I M ∞ := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    have hji : j ≠ i := fun h => hi (by simp [h])
    have hnot : i ∉ is := fun h => hi (List.mem_cons_of_mem _ h)
    simp only [composeFamily, Pi.single_eq_of_ne hji, hzero, ih hnot, Diffeomorph.refl_trans]

theorem composeFamily_single [DecidableEq iota]
    (Phi : iota → ℝ → Diffeomorph I I M M ∞)
    (hzero : ∀ i, Phi i 0 = Diffeomorph.refl I M ∞)
    (is : List iota) (hnodup : is.Nodup) (i : iota) (hi : i ∈ is) (t : ℝ) :
    composeFamily Phi is (Pi.single i t) = Phi i t := by
  induction is with
  | nil => simp at hi
  | cons j is ih =>
    obtain ⟨hj, htail⟩ := List.nodup_cons.mp hnodup
    by_cases hji : j = i
    · subst j
      simp only [composeFamily, Pi.single_eq_same,
        composeFamily_single_of_not_mem Phi hzero is i hj t, Diffeomorph.trans_refl]
    · have hmem : i ∈ is := (List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simp only [composeFamily, Pi.single_eq_of_ne hji, hzero,
        ih htail hmem, Diffeomorph.refl_trans]

theorem composeFamily_contMDiffOn
    (Phi : iota → ℝ → Diffeomorph I I M M ∞) (S : Set (iota → ℝ))
    (hPhi : ∀ i, ContMDiffOn (𝓘(ℝ, iota → ℝ).prod I) I ∞
      (fun q : (iota → ℝ) × M => Phi i (q.1 i) q.2) (S ×ˢ univ))
    (is : List iota) :
    ContMDiffOn (𝓘(ℝ, iota → ℝ).prod I) I ∞
      (fun q : (iota → ℝ) × M => composeFamily Phi is q.1 q.2) (S ×ˢ univ) := by
  induction is with
  | nil => exact contMDiff_snd.contMDiffOn
  | cons i is ih =>
    exact ih.comp (contMDiff_fst.contMDiffOn.prodMk (hPhi i))
      (fun q hq => ⟨hq.1, mem_univ _⟩)

theorem composeFamily_symm_contMDiffOn
    (Phi : iota → ℝ → Diffeomorph I I M M ∞) (S : Set (iota → ℝ))
    (hPhi : ∀ i, ContMDiffOn (𝓘(ℝ, iota → ℝ).prod I) I ∞
      (fun q : (iota → ℝ) × M => (Phi i (q.1 i)).symm q.2) (S ×ˢ univ))
    (is : List iota) :
    ContMDiffOn (𝓘(ℝ, iota → ℝ).prod I) I ∞
      (fun q : (iota → ℝ) × M => (composeFamily Phi is q.1).symm q.2) (S ×ˢ univ) := by
  induction is with
  | nil => exact contMDiff_snd.contMDiffOn
  | cons i is ih =>
    exact (hPhi i).comp (contMDiff_fst.contMDiffOn.prodMk ih)
      (fun q hq => ⟨hq.1, mem_univ _⟩)

def parameterBox (T : iota → ℝ) : Set (iota → ℝ) :=
  {p | ∀ i, p i ∈ Ioo (-T i) (T i)}

theorem parameterBox_isOpen (T : iota → ℝ) : IsOpen (parameterBox T) := by
  have heq : parameterBox T = ⋂ i, (fun p : iota → ℝ => p i) ⁻¹' Ioo (-T i) (T i) := by
    ext p
    simp only [parameterBox, mem_setOf_eq, mem_iInter, mem_preimage]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

theorem zero_mem_parameterBox {T : iota → ℝ} (hT : ∀ i, 0 < T i) :
    0 ∈ parameterBox T := fun i => ⟨neg_lt_zero.mpr (hT i), hT i⟩

theorem family_parameter_contMDiffOn
    (Phi : iota → ℝ → Diffeomorph I I M M ∞) (T : iota → ℝ)
    (hPhi : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Phi i q.1 q.2) (Ioo (-T i) (T i) ×ˢ univ)) (i : iota) :
    ContMDiffOn (𝓘(ℝ, iota → ℝ).prod I) I ∞
      (fun q : (iota → ℝ) × M => Phi i (q.1 i) q.2) (parameterBox T ×ˢ univ) := by
  have heval : ContMDiff (𝓘(ℝ, iota → ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : (iota → ℝ) × M => q.1 i) :=
    (contDiff_apply ℝ ℝ i).contMDiff.comp contMDiff_fst
  exact (hPhi i).comp (heval.prodMk contMDiff_snd).contMDiffOn
    (fun q hq => ⟨hq.1 i, mem_univ _⟩)

end FiniteComposition


theorem exists_spatial_parameter_family (k : ℕ)
    (V : Fin k → (x : M) → TangentSpace I x)
    (hV : ∀ i, ContMDiff I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V i x⟩ : TangentBundle I M))) :
    ∃ U : Set (Fin k → ℝ), IsOpen U ∧ 0 ∈ U ∧
      ∃ Phi : (Fin k → ℝ) → Diffeomorph I I M M ∞,
        Phi 0 = Diffeomorph.refl I M ∞ ∧
        ContMDiffOn (𝓘(ℝ, Fin k → ℝ).prod I) I ∞
          (fun q : (Fin k → ℝ) × M => Phi q.1 q.2) (U ×ˢ univ) ∧
        ContMDiffOn (𝓘(ℝ, Fin k → ℝ).prod I) I ∞
          (fun q : (Fin k → ℝ) × M => (Phi q.1).symm q.2) (U ×ˢ univ) ∧
        ∀ (i : Fin k) (x : M), HasMFDerivAt 𝓘(ℝ, ℝ) I
          (fun t => Phi (Pi.single i t) x) 0
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V i x)) := by
  classical
  choose T hT psi hzero hinv hsmooth hderiv using
    fun i => exists_signed_diffeomorph_family (V i) (hV i)
  have hinvSmooth (i : Fin k) : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (psi i q.1).symm q.2) (Ioo (-T i) (T i) ×ˢ univ) := by
    have hneg : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => -q.1) := contDiff_neg.contMDiff.comp contMDiff_fst
    have hh := (hsmooth i).comp (hneg.prodMk contMDiff_snd).contMDiffOn
      (fun q (hq : q ∈ Ioo (-T i) (T i) ×ˢ (univ : Set M)) =>
        ⟨⟨by linarith [hq.1.2], by linarith [hq.1.1]⟩, mem_univ _⟩)
    exact hh.congr (fun q hq => congrArg (fun f : Diffeomorph I I M M ∞ => f q.2)
      (hinv i q.1 hq.1).symm)
  let Phi := composeFamily psi (List.finRange k)
  refine ⟨parameterBox T, parameterBox_isOpen T, zero_mem_parameterBox hT,
    Phi, composeFamily_zero psi hzero _,
    composeFamily_contMDiffOn psi _ (family_parameter_contMDiffOn psi T hsmooth) _,
    composeFamily_symm_contMDiffOn psi _
      (family_parameter_contMDiffOn (fun i t => (psi i t).symm) T hinvSmooth) _, ?_⟩
  intro i x
  have heq : (fun t => Phi (Pi.single i t) x) = fun t => psi i t x := by
    funext t
    rw [show Phi (Pi.single i t) = psi i t from
      composeFamily_single psi hzero _ (List.nodup_finRange k) i (List.mem_finRange i) t]
  rw [heq]
  have hd := hderiv i 0 ⟨neg_lt_zero.mpr (hT i), hT i⟩ x
  rw [hzero i] at hd
  exact hd

theorem hasMFDerivAt_of_axes {k : ℕ} (f : (Fin k → ℝ) → M)
    (e : (Fin k → ℝ) →L[ℝ] E)
    (hf : MDifferentiableAt 𝓘(ℝ, Fin k → ℝ) I f 0)
    (haxis : ∀ i : Fin k, HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun t => f (Pi.single i t)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (e (Pi.single i 1)))) :
    HasMFDerivAt 𝓘(ℝ, Fin k → ℝ) I f 0 e := by
  have heq : mfderiv 𝓘(ℝ, Fin k → ℝ) I f 0 = e := by
    have hlin : (mfderiv 𝓘(ℝ, Fin k → ℝ) I f 0).toLinearMap = e.toLinearMap := by
      apply (Pi.basisFun ℝ (Fin k)).ext
      intro i
      let L : ℝ →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.single ℝ (fun _ => ℝ) i
      have hsingle : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin k → ℝ)
          (fun t => Pi.single i t) 0 L := L.hasFDerivAt.hasMFDerivAt
      have hchain : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => f (Pi.single i t)) 0
          ((mfderiv 𝓘(ℝ, Fin k → ℝ) I f 0).comp L) := by
        have h0 : Pi.single i (0 : ℝ) = (0 : Fin k → ℝ) := by simp
        have hd : HasMFDerivAt 𝓘(ℝ, Fin k → ℝ) I f (Pi.single i 0)
            (mfderiv 𝓘(ℝ, Fin k → ℝ) I f 0) := by
          rw [h0]
          exact hf.hasMFDerivAt
        exact hd.comp 0 hsingle
      have hcomp := hchain.mfderiv.symm.trans (haxis i).mfderiv
      have hv := congrArg (fun A : ℝ →L[ℝ] E => A 1) hcomp
      change mfderiv 𝓘(ℝ, Fin k → ℝ) I f 0 (Pi.single i 1) =
        (1 : ℝ) • e (Pi.single i 1) at hv
      rw [Pi.basisFun_apply]
      change mfderiv 𝓘(ℝ, Fin k → ℝ) I f 0 (Pi.single i 1) = e (Pi.single i 1)
      exact hv.trans (one_smul ℝ _)
    ext p
    exact congrArg (fun L : (Fin k → ℝ) →ₗ[ℝ] TangentSpace I (f 0) => L p) hlin
  rw [← heq]
  exact hf.hasMFDerivAt


theorem exists_coordinate_parameter_family (x : M) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ 0 ∈ U ∧
      ∃ Phi : (Fin n → ℝ) → Diffeomorph I I M M ∞,
        Phi 0 = Diffeomorph.refl I M ∞ ∧
        ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
          (fun q : (Fin n → ℝ) × M => Phi q.1 q.2) (U ×ˢ univ) ∧
        ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
          (fun q : (Fin n → ℝ) × M => (Phi q.1).symm q.2) (U ×ˢ univ) ∧
        HasMFDerivAt 𝓘(ℝ, Fin n → ℝ) I (fun p => Phi p x) 0
          ((DeTurckNative.chartFrameBasis x x (mem_chart_source E x)).equivFunL.symm :
            (Fin n → ℝ) →L[ℝ] TangentSpace I x) := by
  classical
  let C : DeTurckCompatibleJetNative.Cutoffs (n := n) x ({x} : Set M) :=
    Classical.choice (DeTurckCompatibleJetNative.exists_cutoffs x isCompact_singleton
      (by intro y hy; simpa only [mem_singleton_iff.mp hy] using mem_chart_source E x))
  have heta : C.eta x = 1 := (C.eta_one x (mem_singleton x)).eq_of_nhds
  have hx : x ∈ tsupport C.eta := subset_tsupport C.eta (by simp [Function.mem_support, heta])
  have hfield (i : Fin n) : C.field i x =
      DeTurckNative.chartFrameBasis x x (mem_chart_source E x) i :=
    ((C.field_eventuallyEq (C.zeta_one x hx) i).eq_of_nhds).trans
      (DeTurckNative.chartFrame_eq_basis x x (mem_chart_source E x) i)
  obtain ⟨U, hU, h0, Phi, hPhi0, hPhi, hPhiInv, haxis⟩ :=
    exists_spatial_parameter_family n (fun i => C.field i) (fun i => (C.field i).contMDiff)
  refine ⟨U, hU, h0, Phi, hPhi0, hPhi, hPhiInv, ?_⟩
  have hslice : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ (fun p => Phi p x) U :=
    hPhi.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun p hp => ⟨hp, mem_univ x⟩)
  apply hasMFDerivAt_of_axes (fun p => Phi p x)
    ((DeTurckNative.chartFrameBasis x x (mem_chart_source E x)).equivFunL.symm :
      (Fin n → ℝ) →L[ℝ] TangentSpace I x)
    ((hslice.contMDiffAt (hU.mem_nhds h0)).mdifferentiableAt (by simp))
  intro i
  have hb : ((DeTurckNative.chartFrameBasis x x (mem_chart_source E x)).equivFunL.symm :
        (Fin n → ℝ) →L[ℝ] TangentSpace I x) (Pi.single i 1) =
      DeTurckNative.chartFrameBasis x x (mem_chart_source E x) i := by
    change (DeTurckNative.chartFrameBasis x x (mem_chart_source E x)).equivFun.symm
      (Pi.single i 1) = _
    simp [Module.Basis.equivFun_symm_apply, Pi.single_apply]
  convert! haxis i x using 1
  congr 1
  exact hb.trans (hfield i).symm


theorem exists_coordinate_parameter_inverse (x : M) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ 0 ∈ U ∧
      ∃ Phi : (Fin n → ℝ) → Diffeomorph I I M M ∞,
        Phi 0 = Diffeomorph.refl I M ∞ ∧
        ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
          (fun q : (Fin n → ℝ) × M => Phi q.1 q.2) (U ×ˢ univ) ∧
        ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod I) I ∞
          (fun q : (Fin n → ℝ) × M => (Phi q.1).symm q.2) (U ×ˢ univ) ∧
        ∃ inv : E → (Fin n → ℝ),
          ContDiffAt ℝ ∞ inv (extChartAt I x x) ∧
          inv (extChartAt I x x) = 0 ∧
          ∀ᶠ y in 𝓝 (extChartAt I x x),
            inv y ∈ U ∧ Phi (inv y) x = (extChartAt I x).symm y := by
  obtain ⟨U, hU, h0, Phi, hPhi0, hPhi, hPhiInv, hder⟩ :=
    exists_coordinate_parameter_family (n := n) x
  let e := extChartAt I x
  let A := (DeTurckNative.chartFrameBasis x x (mem_chart_source E x)).equivFunL.symm.trans
    (DeTurckNative.chartDifferentialEquiv x x (mem_chart_source E x))
  let f : (Fin n → ℝ) → E := fun p => e (Phi p x)
  have hPhi0x : Phi 0 x = x := by rw [hPhi0]; rfl
  have hslice : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (fun p => Phi p x) 0 :=
    (hPhi.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun p hp => ⟨hp, mem_univ x⟩)).contMDiffAt (hU.mem_nhds h0)
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ e (Phi 0 x) := by
    rw [hPhi0x]
    exact contMDiffAt_extChartAt
  have hf : ContDiffAt ℝ ∞ f 0 := (hchart.comp 0 hslice).contDiffAt
  have hchartDeriv : HasMFDerivAt I 𝓘(ℝ, E) e (Phi 0 x)
      (DeTurckNative.chartDifferentialEquiv x x (mem_chart_source E x) :
        TangentSpace I x →L[ℝ] E) := by
    rw [hPhi0x, DeTurckNative.chartDifferentialEquiv_coe]
    have hm : MDifferentiableAt I 𝓘(ℝ, E) e x :=
      mdifferentiableAt_extChartAt (mem_chart_source E x)
    exact hm.hasMFDerivAt
  have hf' : HasFDerivAt f (A : (Fin n → ℝ) →L[ℝ] E) 0 := by
    exact (hchartDeriv.comp 0 hder).hasFDerivAt
  have hf0 : f 0 = e x := by dsimp only [f]; rw [hPhi0x]
  let inv := hf.localInverse hf' (by simp)
  have hinv : ContDiffAt ℝ ∞ inv (e x) := by
    rw [← hf0]
    exact hf.to_localInverse hf' (by simp)
  have hinv0 : inv (e x) = 0 := by
    rw [← hf0]
    exact hf.localInverse_apply_image hf' (by simp)
  have htend : Tendsto inv (𝓝 (e x)) (𝓝 0) := by
    simpa only [hinv0] using hinv.continuousAt.tendsto
  have hpoint : Tendsto (fun y => Phi (inv y) x) (𝓝 (e x)) (𝓝 x) := by
    simpa only [hPhi0x, Function.comp_def] using hslice.continuousAt.tendsto.comp htend
  have hright : ∀ᶠ y in 𝓝 (e x), f (inv y) = y := by
    rw [← hf0]
    exact (hf.hasStrictFDerivAt' hf' (by simp)).eventually_right_inverse
  refine ⟨U, hU, h0, Phi, hPhi0, hPhi, hPhiInv, inv, hinv, hinv0, ?_⟩
  filter_upwards [htend (hU.mem_nhds h0),
    hpoint (show e.source ∈ 𝓝 x from extChartAt_source_mem_nhds x), hright]
      with y hyU hySource hy
  refine ⟨hyU, ?_⟩
  calc
    Phi (inv y) x = e.symm (e (Phi (inv y) x)) := (e.left_inv hySource).symm
    _ = e.symm y := congrArg e.symm hy

end PoincareConjecture.DeTurckSpatialParameterNative

end
