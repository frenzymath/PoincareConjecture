import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Cutting.RelativeEndpointChart

/-!
# Labelled relative corners across an arbitrary circle seam

Rotation changes only the scalar phase. The original chart transitions,
old-boundary label, phase-face label and common-corner fixing are retained.
See Waldhausen 1968, Section 1.3, pp. 59--60.
-/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76.HamiltonIntervalTorus

theorem exists_relative_shifted_circle_endpoint_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E)
    (p : ℝ) [Fact (0 < p)] {R : Set X} (q : R → AddCircle p)
    {c a b theta d : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (htheta : theta = a ∨ theta = b) (hd : (d : AddCircle p) = (theta : AddCircle p))
    (psi ell : E →ᴬ[ℝ] ℝ) (u v : E) (T : OpenPartialHomeomorph X E)
    (hpu : psi.contLinear u = 1) (hlv : ell.contLinear v = 1)
    (hpv : psi.contLinear v = 0) {x : X} (hx : x ∈ T.source)
    (hpx : psi (T x) = 0) (hlx : ell (T x) = 0)
    (hT : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E)
    (hR : ∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y))
    (hB : ∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0)
    (hq : ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d : ℝ) : AddCircle p)) :
    ∃ (lambda : E →ᴬ[ℝ] ℝ) (G : OpenPartialHomeomorph X E),
      x ∈ G.source ∧ G.source ⊆ T.source ∧ psi (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      (∀ y ∈ G.source, psi (T y) = 0 → ell (T y) = 0 → G y = T y) ∧
      (∀ y ∈ G.source,
        (∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ AddCircle.closedIntervalArc p a b) ↔
          0 ≤ psi (G y)) ∧
      (∀ y ∈ G.source,
        (y ∈ frontier R ∧ ∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ AddCircle.closedIntervalArc p a b) ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
      ∀ y ∈ G.source,
        (∃ hy : y ∈ R, q ⟨y, hy⟩ = (theta : AddCircle p)) ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  let q' : R → AddCircle p := fun y => q y - (c : AddCircle p)
  have hphase (y : R) (t : ℝ) : q' y = ((t - c : ℝ) : AddCircle p) ↔
      q y = (t : AddCircle p) := by
    change q y - (c : AddCircle p) = ((t - c : ℝ) : AddCircle p) ↔ _
    rw [AddCircle.coe_sub, sub_left_inj]
  have harc (y : R) : q' y ∈ AddCircle.closedIntervalArc p (a - c) (b - c) ↔
      q y ∈ AddCircle.closedIntervalArc p a b := by
    constructor
    · rintro ⟨t, ht, hty⟩
      refine ⟨t + c, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      exact ((hphase y (t + c)).mp (by simpa only [add_sub_cancel_right] using hty.symm)).symm
    · rintro ⟨t, ht, hty⟩
      exact ⟨t - c, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        ((hphase y t).mpr hty.symm).symm⟩
  have htheta' : theta - c = a - c ∨ theta - c = b - c :=
    htheta.imp (fun h => congrArg (fun t => t - c) h)
      (fun h => congrArg (fun t => t - c) h)
  have hd' : ((d - c : ℝ) : AddCircle p) = ((theta - c : ℝ) : AddCircle p) := by
    simp only [AddCircle.coe_sub, hd]
  have hq' (y : R) (hy : (y : X) ∈ T.source) :
      q' y = ((ell (T y) + (d - c) : ℝ) : AddCircle p) := by
    change q y - (c : AddCircle p) = _
    rw [hq y hy, ← AddCircle.coe_sub]
    congr 1
    ring
  obtain ⟨lambda, G, hxG, hGT, hpxG, hG, hfix, hGN, hGB, hGS⟩ :=
    exists_relative_circle_endpoint_chart e p q'
      (by linarith : 0 < a - c) (by linarith : a - c < b - c)
      (by linarith : b - c < p) htheta' hd' psi ell u v T
      hpu hlv hpv hx hpx hlx hT hR hB hq'
  refine ⟨lambda, G, hxG, hGT, hpxG, hG, hfix, ?_, ?_, ?_⟩
  · intro y hy
    simpa only [harc] using hGN y hy
  · intro y hy
    simpa only [harc] using hGB y hy
  · intro y hy
    simpa only [hphase] using hGS y hy

end PoincareMT.M76.HamiltonIntervalTorus

