import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Perturbation.Ambient
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Critical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Isolated
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P := E2 × Real

theorem exists_ambient_shift_of_morse_critical_point
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (v : E3) (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 -> Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hform : ∀ x ∈ e.source, inner Real (v : E3) (f (e x)) =
      inner Real (v : E3) (f p) + ∑ i : Fin 2, σ i * x i ^ 2)
    {ε : Real} (hε : 0 < ε) {A : Set Real} (hA : A.Finite) :
    ∃ (K : Set E3) (a : Real)
        (Phi : Real -> Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      IsCompact K ∧ |a| < ε ∧ inner Real (v : E3) (f p) + a ∉ A ∧
      (∀ y, Phi 0 y = y) ∧
      ContDiff Real ∞ (fun z : Real × E3 => Phi z.1 z.2) ∧
      (∀ s y, y ∉ K -> Phi s y = y) ∧
      (∀ s q, mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : E3) (Phi s (f q))) q = 0 ↔
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (v : E3) (f q)) q = 0) ∧
      (∀ s, (fun q => inner Real (v : E3) (Phi s (f q))) =ᶠ[𝓝 p]
        (fun q => inner Real (v : E3) (f q) + Real.smoothTransition s * a)) ∧
      ∀ q, mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : E3) (f q)) q = 0 -> q ≠ p ->
        ∀ s, (fun u => inner Real (v : E3) (Phi s (f u))) =ᶠ[𝓝 q]
          (fun u => inner Real (v : E3) (f u)) := by
  obtain ⟨F, hF0, hFs, hFp, hF, hFi, hFformula, hsection, hheight⟩ :=
    exists_ambient_morse_coordinates_exact hf v p hp e he0 hep he hei σ hform
  obtain ⟨d, hd, hdball⟩ := Metric.mem_nhds_iff.mp (F.open_source.mem_nhds hF0)
  let R := d / 2
  have hR : 0 < R := half_pos hd
  have hcylinder : closedBall (0 : E2) R ×ˢ closedBall (0 : Real) R ⊆ F.source := by
    rw [closedBall_prod_same]
    exact (closedBall_subset_ball (half_lt_self hd)).trans hdball
  let h : E2 -> Real := fun x => inner Real (v : E3) (f p) + ∑ i, σ i * x i ^ 2
  have hh : ContDiff Real ∞ h :=
    Poincare.Analysis.Calculus.Morse.contDiff_diagonal_quadratic _ _
  have hσne (i : Fin 2) : σ i ≠ 0 := by
    rcases hσ i with hi | hi <;> simp [hi]
  have hcrit (x : E2) : fderiv Real h x = 0 ↔ x = 0 :=
    Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff _ _ hσne x
  have hregular : ∀ x ∈ closedBall (0 : E2) R \ ball 0 (R / 2), fderiv Real h x ≠ 0 := by
    intro x hx hzero
    exact hx.2 ((hcrit x).mp hzero ▸ mem_ball_self (half_pos hR))
  obtain ⟨K, b, a, Phi, hK, hKt, hb, hbR, hbone, ha, havoid, hPhi0,
      hPhis, hPhifix, hPhicoord, hPhiheight, hPhicrit⟩ :=
    exists_ambient_height_shift_in_coordinates F hF hFi (v : E3) hh hheight
      (half_pos hR) (half_lt_self hR) hR hε hcylinder hregular hA
  let height : S2 -> Real := fun q => inner Real (v : E3) (f q)
  let moved (s : Real) : S2 -> Real := fun q => inner Real (v : E3) (Phi s (f q))
  have hsmooth : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ height :=
    (innerSL Real (v : E3)).contMDiff.comp hf.contMDiff
  have hmoved (s : Real) : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (moved s) :=
    (innerSL Real (v : E3)).contMDiff.comp ((Phi s).contMDiff.comp hf.contMDiff)
  have houtside (s : Real) {q : S2} (hq : f q ∉ K) : moved s =ᶠ[𝓝 q] height := by
    filter_upwards [hf.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (hK.isClosed.isOpen_compl.mem_nhds hq)] with u hu
    change inner Real (v : E3) (Phi s (f u)) = inner Real (v : E3) (f u)
    rw [hPhifix s _ hu]
  have hzeroformula (s : Real) {x : E2} (hx : (x, 0) ∈ F.source) :
      moved s (e x) = h x + Real.smoothTransition s * a * b x := by
    have hfzero : F (x, 0) = f (e x) := by simpa using hFformula (x, 0) hx
    simpa only [moved, ← hfzero] using hPhiheight s x hx
  refine ⟨K, a, Phi, hK, ha, ?_, hPhi0, hPhis, hPhifix, ?_, ?_, ?_⟩
  · simpa [h] using havoid
  · intro s q
    change mfderiv (𝓡 2) 𝓘(Real, Real) (moved s) q = 0 ↔
      mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0
    by_cases hq : f q ∈ F.target
    · obtain ⟨z, ⟨hz, hz0⟩, heq⟩ := hsection ▸ (show f q ∈ range f ∩ F.target from ⟨⟨q, rfl⟩, hq⟩)
      have hz' : (z.1, 0) ∈ F.source := by
        have hzpair : z = (z.1, 0) := Prod.ext rfl hz0
        rwa [← hzpair]
      have hex : e z.1 = q := hf.isEmbedding.injective (by
        rw [hFformula z hz, hz0, zero_smul, add_zero] at heq
        exact heq)
      have hx : z.1 ∈ e.source := (hFs hz).1
      have hlocal : moved s ∘ e =ᶠ[𝓝 z.1]
          (fun y => h y + (Real.smoothTransition s * a) * b y) := by
        filter_upwards [(F.open_source.preimage
          (continuous_id.prodMk continuous_const)).mem_nhds hz'] with y hy
        exact hzeroformula s hy
      rw [← hex, mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eventuallyEq
        (hmoved s) e he hei hx hlocal, hPhicrit s z.1,
        mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eqOn hsmooth e he hei hx hform]
    · rw [(houtside s (fun hqK => hq (hKt hqK))).mfderiv_eq]
  · intro s
    have hpt : p ∈ e.target := hep ▸ e.map_source he0
    have heip : e.symm p = 0 := by rw [← hep, e.left_inv he0]
    have hinner : ∀ᶠ x in 𝓝 (0 : E2), x ∈ ball 0 (R / 2) ∧ (x, 0) ∈ F.source := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (x := (0 : E2)) (half_pos hR)),
        (F.open_source.preimage (continuous_id.prodMk continuous_const)).mem_nhds hF0]
        with x hx hy
      exact ⟨hx, hy⟩
    have hnear := (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hpt)).tendsto
    rw [heip] at hnear
    filter_upwards [e.open_target.mem_nhds hpt, hnear.eventually hinner] with q hqt hqx
    have hx : e.symm q ∈ e.source := e.map_target hqt
    have hbone' : b (e.symm q) = 1 := hbone (ball_subset_closedBall hqx.1)
    change moved s q = height q + Real.smoothTransition s * a
    rw [← e.right_inv hqt, hzeroformula s hqx.2, hbone', mul_one]
    exact congrArg (fun t => t + Real.smoothTransition s * a) (hform _ hx).symm
  · intro q hq hqp s
    apply houtside s
    intro hqK
    exact hqp ((height_critical_iff_eq_of_exact_morse_coordinates hf v p e he0 hep he hei
      σ hσ hform F hFs hFformula hsection q (hKt hqK)).mp hq)

end Poincare.Manifold.Schoenflies
