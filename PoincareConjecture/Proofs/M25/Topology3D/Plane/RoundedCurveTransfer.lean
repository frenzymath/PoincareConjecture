import PoincareConjecture.Proofs.M25.Topology3D.Plane.Tube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.UniformRoundedSamples
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PositiveTubeGraph










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_rounded_inscribed_curve_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (hi : ∀ z ∈ Icc a b, Injective (c z))
    (hm : ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c z) q)) :
    ∃ m : ℝ, 0 < m ∧ ∃ n : ℕ, ∃ hn : 3 ≤ n,
      have : NeZero n := ⟨by omega⟩
      let h : ℝ := 2 * Real.pi / n
      let p : ℝ → Polygon E n := fun z =>
        inscribedPolygon (fun t => c z (sphereCircleParameter e t))
          (fun i : Fin (n + 1) => h * (i.val : ℝ))
      0 < h ∧ h < ε ∧
      (∀ z ∈ Icc (a - m / 2) (b + m / 2), IsSimplePolygon (p z)) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
        (∀ s, δ ≤ |s| → ρ s = |s|) →
        (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) →
        (∀ s, |deriv ρ s| ≤ 1) →
        ∃ F : ℝ → (E ≃ₘ[ℝ] E),
          ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
          ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
          (∃ Q : Set E, IsCompact Q ∧
            ∀ z x, x ∉ Q → F z x = x ∧ (F z).symm x = x) ∧
          (∀ z, HasCompactSupport (fun x => F z x - x) ∧
            HasCompactSupport (fun x => (F z).symm x - x)) ∧
          ∀ z ∈ Icc a b, range (fun q : sphere (0 : E) 1 => F z (c z q)) =
            range (roundedPolygonParameter ρ (p z)) := by
  obtain ⟨m, hm0, w, hw0, hw1, T, hs, he, hfwd, hInv⟩ := exists_curveAnnularTube o q0 c hc hab hi hm
  let K := Icc (a - m / 2) (b + m / 2)
  have hKband {z : ℝ} (hz : z ∈ K) : z ∈ Ioo (a - m) (b + m) := by
    constructor <;> dsimp only [K, mem_Icc] at hz <;> linarith [hz.1, hz.2]
  have hx (y : ℝ × E) (hy : y ∈ T.target) : (T.symm y).2 ≠ 0 :=
    (curveAnnularTube_coordinates o q0 c T hw1 hs he hy).1
  have hcoords (z : ℝ) (hz : z ∈ K) (q : sphere (0 : E) 1) :
      (z, c z q) ∈ T.target ∧ curveTubeProjection q0 T (z, c z q) = q ∧
        curveTubeHeight T (z, c z q) = 0 := by
    simpa only [zero_smul, add_zero] using
      curveAnnularTube_coordinates_apply o q0 c T hw1 hs he z (hKband hz) q
        (r := 0) (by simpa only [abs_zero] using hw0)
  let C : ℝ → ℝ → E := fun z t => c z (sphereCircleParameter e t)
  have hC : ContDiff ℝ ∞ (fun p : ℝ × ℝ => C p.1 p.2) :=
    contDiff_curveFamily_circleParameter e c hc
  have hCper (z : ℝ) : Periodic (C z) (2 * Real.pi) := by
    intro t
    exact congrArg (c z) (periodic_sphereCircleParameter e t)
  have hA : 0 < w / 2 := half_pos hw0
  obtain ⟨n, hn, hgrid⟩ := exists_uniform_rounded_tube_samples e q0 T hInv hx
    (show IsCompact K from isCompact_Icc) C hC hCper
    (fun z hz s _ => (hcoords z hz (sphereCircleParameter e s)).1)
    (fun z hz s => (hcoords z hz (sphereCircleParameter e s)).2.1)
    (fun z hz s _ => (hcoords z hz (sphereCircleParameter e s)).2.2) hA hε
  have : NeZero n := ⟨by omega⟩
  let h : ℝ := 2 * Real.pi / n
  obtain ⟨hh, hhε, hsimple, hround⟩ := hgrid
  refine ⟨m, hm0, n, hn, hh, hhε, hsimple, ?_⟩
  intro δ hδ hδhalf ρ hρ htail hbound hderiv
  let G : ℝ → ℝ → E := fun z t =>
    roundedVertexPath ρ (fun j : ℤ => C z (h * (j : ℝ))) (t / h)
  obtain ⟨hG, hGper, hest⟩ := hround δ hδ hδhalf ρ hρ htail hbound hderiv
  have hgood {z : ℝ} (hz : z ∈ Ioo (a - m / 2) (b + m / 2)) : z ∈ K :=
    ⟨hz.1.le, hz.2.le⟩
  obtain ⟨F, hF, hFinv, hQ, hcompact, hrange⟩ := exists_positive_tube_curve_transport
    e o q0 c T hw1 hs he hfwd hInv
    (L := a - m / 2) (U := b + m / 2) (a := a) (b := b)
    (by linarith) (by linarith) (by linarith) (by linarith) hA (by linarith)
    G hG hGper (fun z hz s hst => (hest z (hgood hz) s hst).1)
    (fun z hz s hst => (hest z (hgood hz) s hst).2.1)
    (fun z hz s hst => (hest z (hgood hz) s hst).2.2)
  refine ⟨F, hF, hFinv, hQ, hcompact, ?_⟩
  intro z hz
  refine (hrange z hz).trans ?_
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hperiod : h * (n : ℝ) = 2 * Real.pi := div_mul_cancel₀ _ hn0
  rw [roundedPolygonParameter_inscribed_uniform ρ (C z) h (hperiod.symm ▸ hCper z)]
  apply Subset.antisymm
  · rintro y ⟨t, rfl⟩
    exact ⟨t / h, rfl⟩
  · rintro y ⟨t, rfl⟩
    refine ⟨t * h, ?_⟩
    change roundedVertexPath ρ (fun j : ℤ => C z (h * (j : ℝ))) ((t * h) / h) = _
    rw [mul_div_cancel_right₀ t hh.ne']

end PoincareConjecture.M25.Topology3D
