import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PushIn
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedPolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicCircle
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CurveFamilyTransport

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_supported_rounded_polygon_push
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    {n : ℕ} [NeZero n] (p : Polygon E n) (hp : IsSimplePolygon p)
    (k : Fin n) (had : IsAdmissibleVertex p k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ ∧ (∀ s, δ ≤ |s| → ρ s = |s|) ∧
      (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) ∧ (∀ s, |deriv ρ s| ≤ 1) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, ∀ t,
        dist (roundedPolygonParameter ρ (polygonPushVertex p k z) t)
          (polygonLinearParameter (polygonPushVertex p k z) t) < ε) ∧
      ∃ F : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun x : ℝ × E => F x.1 x.2) ∧
        ContDiff ℝ ∞ (fun x : ℝ × E => (F x.1).symm x.2) ∧
        (∃ K : Set E, IsCompact K ∧ ∀ z x, x ∉ K → F z x = x ∧ (F z).symm x = x) ∧
        (∀ z, HasCompactSupport (fun x => F z x - x) ∧
          HasCompactSupport (fun x => (F z).symm x - x)) ∧
        (∀ x, F 0 x = x) ∧ ∀ z ∈ Icc (0 : ℝ) 1,
          F z '' range (roundedPolygonParameter ρ p) =
            range (roundedPolygonParameter ρ (polygonPushVertex p k z)) := by
  let : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ E = 2)]
    norm_num)
  let P : ℝ → Polygon E n := polygonPushVertex p k
  have hP (i : Fin n) : ContDiff ℝ ∞ (fun z => P z i) :=
    contDiff_polygonPushVertex_apply k i (fun _ => contDiff_const) contDiff_id
  have hsimple (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : IsSimplePolygon (P z) :=
    hp.isSimple_polygonPushVertex k had hz
  obtain ⟨δ, hδ, hd, ρ, hρ, htail, hbound, hder, hγ, hper, hinj, hreg, herr⟩ :=
    exists_smooth_rounded_polygon_family isCompact_Icc P hP hsimple hε
  have hn : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  let γ : ℝ → ℝ → E := fun z => roundedPolygonParameter ρ (P z)
  let C : ℝ → sphere (0 : E) 1 → E := fun z => periodicCircleCurve (n : ℝ) e (γ z)
  have hC : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun x : ℝ × sphere (0 : E) 1 => C x.1 x.2) :=
    contMDiff_periodicCircleCurve_family hn e γ hγ hper
  have hCi (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : Injective (C z) :=
    injective_periodicCircleCurve hn e (hper z) (hinj z hz)
  have hCm (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (q : sphere (0 : E) 1) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (C z) q) :=
    mfderiv_periodicCircleCurve_injective hn e (hper z)
      (hγ.comp (contDiff_const.prodMk contDiff_id)) (hreg z hz) q
  obtain ⟨F, hF, hFi, hK, hsupport, hF0, hFrange⟩ :=
    exists_supported_curve_family_transport e o q0 C hC zero_lt_one hCi hCm
  have hCrange (z : ℝ) : range (C z) = range (γ z) :=
    range_periodicCircleCurve hn e (hper z)
  have hC0 : range (C 0) = range (roundedPolygonParameter ρ p) := by
    rw [hCrange]
    simp only [γ, P, polygonPushVertex_zero]
  refine ⟨δ, hδ, hd, ρ, hρ, htail, hbound, hder, herr,
    F, hF, hFi, hK, hsupport, hF0, ?_⟩
  intro z hz
  rw [← hC0, ← range_comp']
  exact (hFrange z hz).trans (hCrange z)

end PoincareConjecture.M25.Topology3D
