import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonRadialFields
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowFirstIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff NNReal Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_common_radial_evolution
    (r : ℝ) (hr : 0 < r)
    (C : ℝ × E2 → E2) (hC : ContDiff ℝ ∞ C) (hsC : HasCompactSupport C)
    (W : Fin 2 → ℝ × E2 → E2)
    (hW : ∀ j : Fin 2, ContDiff ℝ ∞ (W j) ∧ HasCompactSupport (W j))
    (hRadial : ∀ (t : ℝ) (x : E2), ⟪x, C (t, x)⟫_ℝ = 0)
    (hCommon : ∀ (j : Fin 2) (t : ℝ) (x : E2), ‖x‖ ≤ r →
      W j (t, x) = C (t, x)) :
    ∃ (KC LC : ℝ≥0) (KW LW : Fin 2 → ℝ≥0)
      (hKC : LipschitzWith KC (clockField C))
      (hLC : ∀ p : ℝ × E2, ‖clockField C p‖ ≤ LC)
      (hKW : ∀ j : Fin 2, LipschitzWith (KW j) (clockField (W j)))
      (hLW : ∀ (j : Fin 2) (p : ℝ × E2), ‖clockField (W j) p‖ ≤ LW j),
      let Psi : ℝ → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
        clockEvolutionDiffeomorph C hKC hLC hC hsC
      let Phi : Fin 2 → ℝ → ℝ →
          Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
        fun j => clockEvolutionDiffeomorph (W j) (hKW j) (hLW j)
          (hW j).1 (hW j).2
      let K : Set E2 := (Prod.snd '' tsupport C) ∪
        ⋃ j : Fin 2, Prod.snd '' tsupport (W j)
      IsCompact K ∧
      (∀ (s t : ℝ) (x : E2),
        Psi s t x = clockEvolution C hKC hLC s t x ∧
        (Psi s t).symm x = clockEvolution C hKC hLC t s x) ∧
      (∀ (j : Fin 2) (s t : ℝ) (x : E2),
        Phi j s t x = clockEvolution (W j) (hKW j) (hLW j) s t x ∧
        (Phi j s t).symm x = clockEvolution (W j) (hKW j) (hLW j) t s x) ∧
      (ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => Psi p.1.1 p.1.2 p.2) ∧
        ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => (Psi p.1.1 p.1.2).symm p.2)) ∧
      (∀ j : Fin 2,
        ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => Phi j p.1.1 p.1.2 p.2) ∧
        ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => (Phi j p.1.1 p.1.2).symm p.2)) ∧
      (∀ (s t : ℝ) (x : E2), ‖Psi s t x‖ = ‖x‖ ∧ ‖(Psi s t).symm x‖ = ‖x‖) ∧
      (∀ (j : Fin 2) (s t : ℝ) (x : E2), ‖x‖ ≤ r →
        Phi j s t x = Psi s t x ∧ (Phi j s t).symm x = (Psi s t).symm x) ∧
      (∀ s t : ℝ,
        tsupport (fun x : E2 => Psi s t x - x) ⊆ K ∧
        tsupport (fun x : E2 => (Psi s t).symm x - x) ⊆ K) ∧
      (∀ (j : Fin 2) (s t : ℝ),
        tsupport (fun x : E2 => Phi j s t x - x) ⊆ K ∧
        tsupport (fun x : E2 => (Phi j s t).symm x - x) ⊆ K) ∧
      (∀ (s t : ℝ) (x : E2), x ∉ K →
        (Psi s t x = x ∧ (Psi s t).symm x = x) ∧
        ∀ j : Fin 2, Phi j s t x = x ∧ (Phi j s t).symm x = x) ∧
      (∀ (j : Fin 2) (s t a : ℝ), 0 ≤ a → a ≤ r →
        (Phi j s t) '' ball (0 : E2) a = ball (0 : E2) a ∧
        (Phi j s t).symm '' ball (0 : E2) a = ball (0 : E2) a ∧
        (Phi j s t) '' closedBall (0 : E2) a = closedBall (0 : E2) a ∧
        (Phi j s t).symm '' closedBall (0 : E2) a = closedBall (0 : E2) a ∧
        (Phi j s t) '' sphere (0 : E2) a = sphere (0 : E2) a ∧
        (Phi j s t).symm '' sphere (0 : E2) a = sphere (0 : E2) a) ∧
      (∀ (j : Fin 2) (s t : ℝ) (x : E2),
        HasDerivAt (fun u : ℝ => Phi j s u x) (W j (t, Phi j s t x)) t) ∧
      ∀ (j : Fin 2) (gamma : ℝ → E2) (a b s : ℝ), s ∈ Ioo a b →
        (∀ t ∈ Ioo a b, HasDerivAt gamma (W j (t, gamma t)) t) →
        EqOn (fun t : ℝ => Phi j s t (gamma s)) gamma (Ioo a b) := by
  classical
  obtain ⟨KC, LC, hKC, hLC⟩ := clockField_bounds C hC hsC
  have hbounds (j : Fin 2) := clockField_bounds (W j) (hW j).1 (hW j).2
  choose KW LW hKW hLW using hbounds
  refine ⟨KC, LC, KW, LW, hKC, hLC, hKW, hLW, ?_⟩
  let Psi := clockEvolutionDiffeomorph C hKC hLC hC hsC
  let Phi (j : Fin 2) :=
    clockEvolutionDiffeomorph (W j) (hKW j) (hLW j) (hW j).1 (hW j).2
  let K : Set E2 := (Prod.snd '' tsupport C) ∪
    ⋃ j : Fin 2, Prod.snd '' tsupport (W j)
  have hK : IsCompact K := (hsC.isCompact.image continuous_snd).union
    (isCompact_iUnion (fun j => (hW j).2.isCompact.image continuous_snd))
  have hswap : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => ((p.1.2, p.1.1), p.2)) :=
    (contDiff_fst.snd.prodMk contDiff_fst.fst).prodMk contDiff_snd
  have hPsiSmooth :
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => Psi p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => (Psi p.1.1 p.1.2).symm p.2) :=
    ⟨clockEvolution_contDiff C hKC hLC hC hsC,
      (clockEvolution_contDiff C hKC hLC hC hsC).comp hswap⟩
  have hPhiSmooth (j : Fin 2) :
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => Phi j p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => (Phi j p.1.1 p.1.2).symm p.2) :=
    ⟨clockEvolution_contDiff (W j) (hKW j) (hLW j) (hW j).1 (hW j).2,
      (clockEvolution_contDiff (W j) (hKW j) (hLW j) (hW j).1 (hW j).2).comp hswap⟩
  let A : ℝ × E2 → ℝ := fun p => ‖p.2‖ ^ 2
  have hA (p : ℝ × E2) : HasFDerivAt A
      (2 • (innerSL ℝ p.2).comp (ContinuousLinearMap.snd ℝ ℝ E2)) p :=
    (ContinuousLinearMap.snd ℝ ℝ E2).hasFDerivAt.norm_sq
  have hzero (p : ℝ × E2) (hp : p ∉ (univ : Set (ℝ × E2))) : clockField C p = 0 :=
    False.elim (hp (mem_univ _))
  have hAf (p : ℝ × E2) (_hp : p ∈ (univ : Set (ℝ × E2))) :
      fderiv ℝ A p (clockField C p) = 0 := by
    rw [(hA p).fderiv]
    simp [clockField, hRadial]
  have hNorm (s t : ℝ) (x : E2) : ‖clockEvolution C hKC hLC s t x‖ = ‖x‖ := by
    have heq := boundedFlow_preserves_firstIntegral (clockField C) hKC hLC hzero
      A (fun p _ => (hA p).differentiableAt) hAf (s, x) (mem_univ _) (t - s)
    change ‖clockEvolution C hKC hLC s t x‖ ^ 2 = ‖x‖ ^ 2 at heq
    nlinarith only [heq, norm_nonneg (clockEvolution C hKC hLC s t x), norm_nonneg x]
  have hPsiNorm (s t : ℝ) (x : E2) :
      ‖Psi s t x‖ = ‖x‖ ∧ ‖(Psi s t).symm x‖ = ‖x‖ :=
    ⟨hNorm s t x, hNorm t s x⟩
  have hAgree (j : Fin 2) (s t : ℝ) (x : E2) (hx : ‖x‖ ≤ r) :
      Phi j s t x = Psi s t x := by
    let gamma : ℝ → E2 := fun u => clockEvolution C hKC hLC s u x
    have hs : s ∈ Ioo (min s t - r) (max s t + r) :=
      ⟨by linarith only [min_le_left s t, hr], by linarith only [le_max_left s t, hr]⟩
    have ht : t ∈ Ioo (min s t - r) (max s t + r) :=
      ⟨by linarith only [min_le_right s t, hr], by linarith only [le_max_right s t, hr]⟩
    have hd (u : ℝ) (_hu : u ∈ Ioo (min s t - r) (max s t + r)) :
        HasDerivAt gamma (W j (u, gamma u)) u := by
      rw [hCommon j u (gamma u) ((hNorm s u x).le.trans hx)]
      exact clockEvolution_hasDerivAt C hKC hLC s u x
    have heq := clockEvolution_tracks (W j) (hKW j) (hLW j) gamma hs hd ht
    change clockEvolution (W j) (hKW j) (hLW j) s t x =
      clockEvolution C hKC hLC s t x
    simpa only [gamma, clockEvolution_self] using heq
  have hAgreement (j : Fin 2) (s t : ℝ) (x : E2) (hx : ‖x‖ ≤ r) :
      Phi j s t x = Psi s t x ∧ (Phi j s t).symm x = (Psi s t).symm x :=
    ⟨hAgree j s t x hx, hAgree j t s x hx⟩
  have hSupport (V : ℝ × E2 → E2) (KV LV : ℝ≥0)
      (hKV : LipschitzWith KV (clockField V))
      (hLV : ∀ p : ℝ × E2, ‖clockField V p‖ ≤ LV)
      (hSub : Prod.snd '' tsupport V ⊆ K) (s t : ℝ) :
      tsupport (fun x => clockEvolution V hKV hLV s t x - x) ⊆ K :=
    closure_minimal ((clockEvolution_support_subset V hKV hLV s t).trans hSub)
      hK.isClosed
  have hSupportC (s t : ℝ) :
      tsupport (fun x : E2 => Psi s t x - x) ⊆ K ∧
      tsupport (fun x : E2 => (Psi s t).symm x - x) ⊆ K :=
    ⟨hSupport C KC LC hKC hLC subset_union_left s t,
      hSupport C KC LC hKC hLC subset_union_left t s⟩
  have hSupportW (j : Fin 2) (s t : ℝ) :
      tsupport (fun x : E2 => Phi j s t x - x) ⊆ K ∧
      tsupport (fun x : E2 => (Phi j s t).symm x - x) ⊆ K := by
    have hj : Prod.snd '' tsupport (W j) ⊆ K :=
      (subset_iUnion (fun k : Fin 2 => Prod.snd '' tsupport (W k)) j).trans subset_union_right
    exact ⟨hSupport (W j) (KW j) (LW j) (hKW j) (hLW j) hj s t,
      hSupport (W j) (KW j) (LW j) (hKW j) (hLW j) hj t s⟩
  have hfixed (f : E2 → E2) (hf : tsupport (fun x => f x - x) ⊆ K)
      (x : E2) (hx : x ∉ K) : f x = x := by
    have hz : (fun y : E2 => f y - y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y : E2 => f y - y)
        (fun h => hx (hf h))
    exact sub_eq_zero.mp hz
  have hFix (s t : ℝ) (x : E2) (hx : x ∉ K) :
      (Psi s t x = x ∧ (Psi s t).symm x = x) ∧
      ∀ j : Fin 2, Phi j s t x = x ∧ (Phi j s t).symm x = x :=
    ⟨⟨hfixed _ (hSupportC s t).1 x hx, hfixed _ (hSupportC s t).2 x hx⟩,
      fun j => ⟨hfixed _ (hSupportW j s t).1 x hx, hfixed _ (hSupportW j s t).2 x hx⟩⟩
  have hImage (f : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞) (S : Set E2)
      (hf : MapsTo f S S) (hi : MapsTo f.symm S S) : f '' S = S ∧ f.symm '' S = S := by
    constructor
    · apply Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hf hx
      · intro y hy
        exact ⟨f.symm y, hi hy, f.apply_symm_apply y⟩
    · apply Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hi hx
      · intro y hy
        exact ⟨f y, hf hy, f.symm_apply_apply y⟩
  have hImages (j : Fin 2) (s t a : ℝ) (_ha : 0 ≤ a) (har : a ≤ r) :
      (Phi j s t) '' ball (0 : E2) a = ball (0 : E2) a ∧
      (Phi j s t).symm '' ball (0 : E2) a = ball (0 : E2) a ∧
      (Phi j s t) '' closedBall (0 : E2) a = closedBall (0 : E2) a ∧
      (Phi j s t).symm '' closedBall (0 : E2) a = closedBall (0 : E2) a ∧
      (Phi j s t) '' sphere (0 : E2) a = sphere (0 : E2) a ∧
      (Phi j s t).symm '' sphere (0 : E2) a = sphere (0 : E2) a := by
    have hn (x : E2) (hx : ‖x‖ ≤ r) :
        ‖Phi j s t x‖ = ‖x‖ ∧ ‖(Phi j s t).symm x‖ = ‖x‖ := by
      rw [(hAgreement j s t x hx).1, (hAgreement j s t x hx).2]
      exact hPsiNorm s t x
    have hb := hImage (Phi j s t) (ball (0 : E2) a)
      (fun x hx => by
        rw [mem_ball_zero_iff] at hx ⊢
        rw [(hn x (hx.le.trans har)).1]
        exact hx)
      (fun x hx => by
        rw [mem_ball_zero_iff] at hx ⊢
        rw [(hn x (hx.le.trans har)).2]
        exact hx)
    have hc := hImage (Phi j s t) (closedBall (0 : E2) a)
      (fun x hx => by
        rw [mem_closedBall_zero_iff] at hx ⊢
        rw [(hn x (hx.trans har)).1]
        exact hx)
      (fun x hx => by
        rw [mem_closedBall_zero_iff] at hx ⊢
        rw [(hn x (hx.trans har)).2]
        exact hx)
    have hs := hImage (Phi j s t) (sphere (0 : E2) a)
      (fun x hx => by
        rw [mem_sphere_zero_iff_norm] at hx ⊢
        rw [(hn x (hx.le.trans har)).1]
        exact hx)
      (fun x hx => by
        rw [mem_sphere_zero_iff_norm] at hx ⊢
        rw [(hn x (hx.le.trans har)).2]
        exact hx)
    exact ⟨hb.1, hb.2, hc.1, hc.2, hs.1, hs.2⟩
  exact ⟨hK, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => ⟨rfl, rfl⟩,
    hPsiSmooth, hPhiSmooth, hPsiNorm, hAgreement, hSupportC, hSupportW,
    hFix, hImages,
    fun j s t x => clockEvolution_hasDerivAt (W j) (hKW j) (hLW j) s t x,
    fun j gamma _ _ _ hs hd => clockEvolution_tracks (W j) (hKW j) (hLW j) gamma hs hd⟩

end PoincareConjecture.M25.Topology3D
