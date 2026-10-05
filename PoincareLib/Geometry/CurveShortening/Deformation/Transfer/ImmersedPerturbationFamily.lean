import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.Transfer.ImmersedPerturbationComposition
import PoincareLib.Geometry.CurveShortening.Deformation.Limit.ImmersedAreaTransfer
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.PeriodicSpeed
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops

/-!
# Genuine loop objects for the finite perturbation family

The actual smooth motions act on the given smooth family's actual
periodic maps. The resulting periodic curves produce frozen C1 loop
objects with exactly those maps, including equality to the original
periodic map at parameter zero. MT Lemma 19.4, pp. 439-441;
M65 derivation 49, sections 1 and 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M65Perturbation

variable {M : Type u} {n : ℕ}

/-- Periodic starting maps and actual periodic weights give a periodic
controlled map. MT Lemma 19.4, pp. 439-441; derivation 49. -/
theorem foldControls_periodic_map
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ)
    (hbeta : ∀ i, Function.Periodic (beta i) curvePeriod)
    (L : List (Fin n)) (p : Fin n → ℝ) (c : ℝ → M)
    (hc : Function.Periodic c curvePeriod) :
    Function.Periodic (fun x => foldControls Phi beta L p x (c x)) curvePeriod := by
  intro x
  change foldControls Phi beta L p (x + curvePeriod) (c (x + curvePeriod)) = _
  rw [hc x]
  exact foldControls_periodic Phi beta hbeta L p (c x) x

variable [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {J : Set ℝ}

/-- The given actual family and genuine finite controls produce a
jointly smooth map in parameters, angle and time on the literal domain.
MT Lemma 19.4, pp. 439-441; derivation 49, section 3. -/
theorem foldControls_family_smooth (F : RicciFlow 3 M (Icc a b))
    (C : M65SmoothFilledLoopFamily F J)
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hbound : ∀ i x, |beta i x| ≤ 1) (L : List (Fin n)) :
    ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => foldControls Phi beta L z.1 z.2.1 (periodicFreeLoop (C.loops z.2.2) z.2.1))
      (ball 0 d ×ˢ (univ ×ˢ J)) := by
  have hC : ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z : (Fin n → ℝ) × (ℝ × ℝ) => periodicFreeLoop (C.loops z.2.2) z.2.1)
      (ball 0 d ×ˢ (univ ×ˢ J)) :=
    C.joint_smooth.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2)
  exact (foldControls_contMDiffOn Phi beta d hPhi hbeta hbound L).comp
    (contDiff_fst.contMDiff.contMDiffOn.prodMk
      (contDiff_snd.fst.contMDiff.contMDiffOn.prodMk hC))
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

set_option maxHeartbeats 600000 in
-- The actual loop constructor retains its total annular extension and its parameter domain.
/-- Genuine finite motions acting on the supplied family produce actual
frozen C1 loop objects with joint smoothness and exact original values at
zero. Genericity is a later conclusion, not an input here.
MT Lemma 19.4, pp. 439-441; derivation 49, sections 1 and 3. -/
theorem exists_controlled_loop_family (F : RicciFlow 3 M (Icc a b))
    (C : M65SmoothFilledLoopFamily F J)
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hperiod : ∀ i, Function.Periodic (beta i) curvePeriod)
    (hbound : ∀ i x, |beta i x| ≤ 1) (L : List (Fin n)) :
    ∃ Gamma : (Fin n → ℝ) → ℝ → C1FreeLoopSpace (M := M),
      (∀ p ∈ ball 0 d, ∀ q ∈ J, ∀ x,
        periodicFreeLoop (Gamma p q) x =
          foldControls Phi beta L p x (periodicFreeLoop (C.loops q) x)) ∧
      ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
        (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1)
        (ball 0 d ×ˢ (univ ×ˢ J)) ∧
      ∀ q ∈ J, ∀ x, periodicFreeLoop (Gamma 0 q) x = periodicFreeLoop (C.loops q) x := by
  classical
  let c (p : Fin n → ℝ) (q x : ℝ) :=
    foldControls Phi beta L p x (periodicFreeLoop (C.loops q) x)
  have hsmooth := foldControls_family_smooth F C Phi beta d hPhi hbeta hbound L
  have hcurve (p : Fin n → ℝ) (q : ℝ) (hp : p ∈ ball 0 d) (hq : q ∈ J) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (c p q) := by
    have hinj : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin n → ℝ) × (ℝ × ℝ)) ∞
        (fun x : ℝ => (p, x, q)) :=
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)).contMDiff
    have hslice : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ (c p q) univ :=
      hsmooth.comp hinj.contMDiffOn (fun _ _ => ⟨hp, mem_univ _, hq⟩)
    exact (contMDiffOn_univ.mp hslice).of_le (by simp)
  have hper (p : Fin n → ℝ) (q : ℝ) : Function.Periodic (c p q) curvePeriod :=
    foldControls_periodic_map Phi beta hperiod L p _
      (Proofs.M58.periodic_periodicFreeLoop (C.loops q))
  let Gamma (p : Fin n → ℝ) (q : ℝ) : C1FreeLoopSpace (M := M) :=
    if h : p ∈ ball 0 d ∧ q ∈ J then m65LoopOfPeriodic (c p q) (hcurve p q h.1 h.2) (hper p q)
    else C.loops q
  have hvalue (p : Fin n → ℝ) (hp : p ∈ ball 0 d) (q : ℝ) (hq : q ∈ J) (x : ℝ) :
      periodicFreeLoop (Gamma p q) x = c p q x := by
    dsimp only [Gamma]
    rw [dif_pos (show p ∈ ball 0 d ∧ q ∈ J from ⟨hp, hq⟩)]
    exact m65PeriodicFreeLoop_loopOfPeriodic _ _ _ x
  refine ⟨Gamma, hvalue, ?_, ?_⟩
  · exact hsmooth.congr (fun z hz => hvalue z.1 hz.1 z.2.2 hz.2.2 z.2.1)
  · intro q hq x
    rw [hvalue 0 (mem_ball_self hd) q hq x]
    exact foldControls_eq_of_zero Phi beta hzero L 0 x _ (fun _ _ => rfl)

end PoincareMT.M65Perturbation
