import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Defs
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Coordinates

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GeodesicVariation.jacobi_of_coefficients
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {S I : Set ℝ}
    (hS : IsOpen S) (hI : IsOpen I) (Γ : GeodesicVariation B S I)
    (A : E → E →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p ∈ S ×ˢ I, ContDiffAt ℝ ∞ A (Γ.phase p).1)
    (hsymm : ∀ p ∈ S ×ˢ I, ∀ a b, A (Γ.phase p).1 a b = A (Γ.phase p).1 b a)
    (heq : ∀ x a b, A x a b = coordinateChristoffel B x a b) :
    ∀ t ∈ I,
      alongCovariantDerivative B (fun τ => (Γ.phase (0, τ)).1)
        (alongCovariantDerivative B
          (fun τ => (Γ.phase (0, τ)).1) (variationField Γ) ·) t +
        ConnectionVariation.christoffelCurvature A (Γ.phase (0, t)).1
          (variationField Γ t) (Γ.phase (0, t)).2 (Γ.phase (0, t)).2 = 0 := by
  let u : ℝ × ℝ → E := fun p => (Γ.phase p).1
  let V : ℝ × ℝ → E := fun p => (Γ.phase p).2
  let ds : ℝ × ℝ := (1, 0)
  let dt : ℝ × ℝ := (0, 1)
  let T : ℝ × ℝ → E := fun p => fderiv ℝ u p dt
  let J : ℝ × ℝ → E := fun p => fderiv ℝ u p ds
  let c : ℝ → ℝ × ℝ := fun t => (0, t)
  have hu {p} (hp : p ∈ S ×ˢ I) : ContDiffAt ℝ ∞ u p :=
    (Γ.smooth.contDiffAt ((hS.prod hI).mem_nhds hp)).fst
  have hV {p} (hp : p ∈ S ×ˢ I) : ContDiffAt ℝ ∞ V p :=
    (Γ.smooth.contDiffAt ((hS.prod hI).mem_nhds hp)).snd
  have hJ {p} (hp : p ∈ S ×ˢ I) : ContDiffAt ℝ ∞ J p :=
    ((hu hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have hc (t : ℝ) : HasDerivAt c dt t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
  have hT {p} (hp : p ∈ S ×ˢ I) : T p = V p := by
    have hcurve : HasDerivAt (fun t => (p.1, t)) dt p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have h := ((hu hp).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2 hcurve
    exact h.unique (Γ.geodesic p.1 hp.1 p.2 hp.2).fst
  have hgeodesic {p} (hp : p ∈ S ×ˢ I) :
      ConnectionVariation.covDerivAlong A u T dt p = 0 := by
    have hev : T =ᶠ[𝓝 p] V := by
      filter_upwards [(hS.prod hI).mem_nhds hp] with q hq
      exact hT hq
    rw [ConnectionVariation.covDerivAlong_congr A u hev dt]
    have hcurve : HasDerivAt (fun t => (p.1, t)) dt p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have h := ((hV hp).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2 hcurve
    have he := h.unique (Γ.geodesic p.1 hp.1 p.2 hp.2).snd
    change fderiv ℝ V p dt = -coordinateChristoffel B (u p) (V p) (V p) at he
    change fderiv ℝ V p dt + A (u p) (T p) (V p) = 0
    rw [he, hT hp, heq, neg_add_cancel]
  have hJcurve {t} (ht : t ∈ I) : J (c t) = variationField Γ t := by
    have hcurve : HasDerivAt (fun s => (s, t)) ds 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 t)
    have hd := ((hu ⟨Γ.base_mem, ht⟩).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hcurve
    symm
    simpa only [variationField, fderiv_eq_smul_deriv, one_smul, u, c, J,
      Function.comp_def] using hd.deriv
  intro t ht
  have hp : c t ∈ S ×ˢ I := ⟨Γ.base_mem, ht⟩
  have hu3 : ContDiffAt ℝ 3 u (c t) := by
    exact (hu hp).of_le
      (WithTop.coe_le_coe.2 (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) by exact le_top))
  have hcomm := ConnectionVariation.covDerivAlong_geodesic_family_jacobi
    (u := u) (Γ := A) (p := c t)
    hu3
    ((hA (c t) hp).differentiableAt (by simp))
    (show ∀ᶠ p in 𝓝 (c t), ∀ a b, A (u p) a b = A (u p) b a from
      Filter.Eventually.mono ((hS.prod hI).mem_nhds hp) fun p hp => hsymm p hp)
    (show ∀ᶠ p in 𝓝 (c t), ConnectionVariation.covDerivAlong A u T dt p = 0 from
      Filter.Eventually.mono ((hS.prod hI).mem_nhds hp) fun _ hp => hgeodesic hp)
    (ds := ds) (dt := dt)
  let W := ConnectionVariation.covDerivAlong A u J dt
  have hW {p} (hp : p ∈ S ×ˢ I) : ContDiffAt ℝ ∞ W p :=
    ConnectionVariation.contDiffAt_covDerivAlong (u := u) (V := J)
      (hA p hp) (hu hp) (hJ hp) dt
  have hrestrict {r} (hr : r ∈ I) : W (c r) =
      alongCovariantDerivative B (fun τ => (Γ.phase (0, τ)).1)
        (variationField Γ) r := by
    have hpr : c r ∈ S ×ˢ I := ⟨Γ.base_mem, hr⟩
    have h := ConnectionVariation.covDerivAlong_comp_curve A
      ((hu hpr).differentiableAt (by simp)) ((hJ hpr).differentiableAt (by simp)) (hc r)
    have hevent : J ∘ c =ᶠ[𝓝 r] variationField Γ :=
      Filter.Eventually.mono (hI.mem_nhds hr) fun s hs => hJcurve hs
    rw [ConnectionVariation.covDerivAlong_congr A (u ∘ c) hevent 1] at h
    change ConnectionVariation.covDerivAlong A u J dt (c r) =
      alongCovariantDerivative B (fun τ => (Γ.phase (0, τ)).1)
        (variationField Γ) r
    simpa only [ConnectionVariation.covDerivAlong, alongCovariantDerivative,
      W, u, c, Function.comp_def, heq] using h.symm
  have houter := ConnectionVariation.covDerivAlong_comp_curve A
    ((hu hp).differentiableAt (by simp)) ((hW hp).differentiableAt (by simp)) (hc t)
  have hWevent : W ∘ c =ᶠ[𝓝 t]
      (alongCovariantDerivative B (fun τ => (Γ.phase (0, τ)).1) (variationField Γ) ·) :=
    Filter.Eventually.mono (hI.mem_nhds ht) fun s hs => hrestrict hs
  rw [ConnectionVariation.covDerivAlong_congr A (u ∘ c) hWevent 1] at houter
  have hout : ConnectionVariation.covDerivAlong A u W dt (c t) =
      alongCovariantDerivative B (fun τ => (Γ.phase (0, τ)).1)
        (alongCovariantDerivative B
          (fun τ => (Γ.phase (0, τ)).1) (variationField Γ) ·) t := by
    change ConnectionVariation.covDerivAlong A u W dt (c t) =
      alongCovariantDerivative B (fun τ => (Γ.phase (0, τ)).1)
        (alongCovariantDerivative B
          (fun τ => (Γ.phase (0, τ)).1) (variationField Γ) ·) t
    simpa only [ConnectionVariation.covDerivAlong, alongCovariantDerivative,
      W, u, c, Function.comp_def, heq] using houter.symm
  change ConnectionVariation.covDerivAlong A u W dt (c t) +
    ConnectionVariation.christoffelCurvature A (u (c t)) (J (c t)) (T (c t)) (T (c t)) = 0 at hcomm
  rw [hout, hJcurve ht, hT hp] at hcomm
  exact hcomm

end PoincareConjecture.CoordinateExponential
