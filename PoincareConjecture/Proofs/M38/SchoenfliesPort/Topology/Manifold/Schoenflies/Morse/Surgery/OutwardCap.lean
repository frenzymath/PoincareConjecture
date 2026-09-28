import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.CappedSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift.Reflection

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private theorem smoothEmbedding_postcompose
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (R ∘ f) := by
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (R.contMDiff.comp hf.contMDiff) (R.injective.comp hf.isEmbedding.injective)
  intro p
  rw [mfderiv_comp p (R.contMDiff.mdifferentiable (by simp) _)
    (hf.contMDiff.mdifferentiable (by simp) p)]
  exact (R.mfderivToContinuousLinearEquiv (by simp) (f p)).injective.comp
    (injective_mfderiv_sphere_embedding hf p)

theorem exists_outward_capped_sphere_of_cylindrical_tube_with_disk_and_range_for_small_scale
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {ε : Real} (hε : 0 < ε)
    {τ : Real} (hτ : 0 < τ)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 -> Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (hcylinder : ∀ p t, t ∈ Ioo (-ε) ε ->
      f (T (p, t)) = (c - t) • v + (γ p : E3))
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hintersection :
      ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun p : S1 => T (p, 0)))
    (e : OpenPartialHomeomorph E2 S2)
    (hesource : closedBall 0 1 ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hecenter : range (fun p : S1 => T (p, 0)) = e '' sphere (0 : E2) 1)
    (henegative : ∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ e '' ball 0 1) :
    ∃ δ : Real, 0 < δ ∧ ∀ s : Real, s < δ -> ∀ hs : 0 < s,
    ∃ d : OpenPartialHomeomorph E2 S2,
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      closedBall 0 1 ⊆ d.source ∧
      d '' closedBall 0 1 = e '' closedBall 0 1 ∧
      d '' ball 0 1 = e '' ball 0 1 ∧
      range (fun p : S1 => T (p, 0)) = d '' sphere (0 : E2) 1 ∧
      (∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ d '' ball 0 1) ∧
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
        ∃ g : E2 -> E3,
          ContDiff Real ∞ g ∧ Injective g ∧
          (∀ x, Injective (fderiv Real g x)) ∧
          (∀ p : S1, g p = f (d p) ∧ g p = c • v + (γ (q p) : E3)) ∧
          (∀ x, ‖x‖ < 1 -> c < inner Real v (g x)) ∧
          (∀ x, |inner Real v (g x) - c| < τ) ∧
          (∃ η : Real, 0 < η ∧ η < 1 ∧
            ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η ->
              ρ • (p : E2) ∈ d.source ∧
              d (ρ • (p : E2)) = T (q p, (-s) * ((1 - ρ ^ 2) / (2 * ρ))) ∧
              g (ρ • (p : E2)) = f (d (ρ • (p : E2)))) ∧
          Disjoint (g '' ball 0 1) (f '' (d '' ball 0 1)ᶜ) ∧
          g '' closedBall (0 : E2) 1 =
            liftPlaneDiffeomorph hv c s hs.ne' A ''
              ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
                {p : S2 | 0 ≤ inner Real v (p : E3)}) ∧
          ∃ f' : S2 -> E3,
            _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f' ∧
            (∀ x ∈ closedBall 0 1, f' (d x) = g x) ∧
            (∀ y ∉ d '' ball 0 1, f' y = f y) ∧
            range f' = g '' closedBall 0 1 ∪ f '' (d '' ball 0 1)ᶜ := by
  let R := heightReflection hv
  let F : S2 -> E3 := R ∘ f
  have hF : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F :=
    smoothEmbedding_postcompose hf R
  have hFcylinder (p : S1) (t : Real) (ht : t ∈ Ioo (-ε) ε) :
      F (T (p, t)) = (-c + t) • v + (γ p : E3) := by
    change heightReflection hv (f (T (p, t))) = _
    rw [hcylinder p t ht, heightReflection_height_add_plane]
    congr 2
    ring
  have hRdisk : (fun x : Hemisphere.Plane v => (-c) • v + (A x : E3)) '' closedBall 0 1 =
      R '' ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) := by
    rw [image_image]
    apply image_congr
    intro x _
    exact (heightReflection_height_add_plane hv c (A x)).symm
  have hFintersection :
      ((fun x : Hemisphere.Plane v => (-c) • v + (A x : E3)) '' closedBall 0 1) ∩
        range F = F '' range (fun p : S1 => T (p, 0)) := by
    change _ ∩ range (R ∘ f) = (R ∘ f) '' _
    have hRinj : Injective (R : E3 -> E3) := R.injective
    rw [hRdisk, range_comp, ← image_inter hRinj, hintersection, image_comp]
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_capped_sphere_of_cylindrical_tube_with_disk_and_range_for_small_scale
      hF hv (-c) hε hτ T hT hTi hsource γ hγ hFcylinder A hboundary hFintersection
      e hesource he hei hecenter henegative
  refine ⟨δ, hδ, ?_⟩
  intro s hsδ hs
  obtain ⟨d, hd, hdi, hds, hdc, hdb, hdcenter, hdnegative,
    q, k, hk, hki, hkd, hkb, hknegative, hkwidth, ⟨η, hη, hη1, hkcollar⟩,
    hkdisjoint, hkrange, f₀, hf₀, hf₀cap, hf₀off, hf₀range⟩ :=
    hsmall (-s) (by linarith) (neg_neg_of_pos hs)
  let g : E2 -> E3 := R ∘ k
  let f' : S2 -> E3 := R ∘ f₀
  have hRR (x : E3) : R (R x) = x := heightReflection_heightReflection hv x
  have hgder (x : E2) : Injective (fderiv Real g x) := by
    have hRd : Injective (fderiv Real R (k x)) := by
      have h := (R.mfderivToContinuousLinearEquiv (by simp) (k x)).injective
      change Injective (mfderiv (𝓡 3) (𝓡 3) R (k x)) at h
      simpa only [mfderiv_eq_fderiv, TangentSpace] using h
    rw [show g = R ∘ k from rfl, fderiv_comp x
      (R.contDiff.differentiable (by simp) (k x)) (hk.differentiable (by simp) x)]
    exact hRd.comp (hkd x)
  have hgf (x : E2) (hx : k x = F (d x)) : g x = f (d x) := by
    change R (k x) = f (d x)
    rw [hx]
    exact hRR _
  have hgdisjoint : Disjoint (g '' ball 0 1) (f '' (d '' ball 0 1)ᶜ) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨p, hp, hpeq⟩
    apply disjoint_left.mp hkdisjoint (mem_image_of_mem k hx)
    refine ⟨p, hp, ?_⟩
    have h := congrArg R hpeq
    change F p = R (R (k x)) at h
    exact h.trans (hRR _)
  have hgrange : g '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv c s hs.ne' A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)}) := by
    change (R ∘ k) '' closedBall 0 1 = _
    rw [image_comp, hkrange]
    convert! image_heightReflection_liftPlaneDiffeomorph hv (-c) (-s)
      (neg_neg_of_pos hs).ne A _ using 1
    simp only [neg_neg]
  refine ⟨d, hd, hdi, hds, hdc, hdb, hdcenter, hdnegative, q, g,
    R.contDiff.comp hk, R.injective.comp hki, hgder, ?_, ?_, ?_, ?_, hgdisjoint,
    hgrange, f', smoothEmbedding_postcompose hf₀ R, ?_, ?_, ?_⟩
  · intro p
    refine ⟨hgf p (hkb p).1, ?_⟩
    change heightReflection hv (k p) = _
    rw [(hkb p).2, heightReflection_height_add_plane, neg_neg]
  · intro x hx
    change c < inner Real v (heightReflection hv (k x))
    rw [inner_heightReflection]
    linarith [hknegative x hx]
  · intro x
    change |inner Real v (heightReflection hv (k x)) - c| < τ
    rw [inner_heightReflection, show -inner Real v (k x) - c =
      -(inner Real v (k x) - -c) by ring, abs_neg]
    exact hkwidth x
  · refine ⟨η, hη, hη1, ?_⟩
    intro p ρ hρ
    obtain ⟨hx, hdval, hkval⟩ := hkcollar p ρ hρ
    exact ⟨hx, hdval, hgf _ hkval⟩
  · intro x hx
    exact congrArg R (hf₀cap x hx)
  · intro y hy
    change R (f₀ y) = f y
    rw [hf₀off y hy]
    exact hRR _
  · change range (R ∘ f₀) = _
    rw [range_comp, hf₀range, image_union, ← image_comp, ← image_comp]
    congr 1
    apply image_congr
    intro x _
    exact hRR (f x)

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
