import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.SliceGerm
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Preparation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem exists_common_cylindrical_preparation_of_surface_germ
    {v : E3} (hv : ‖v‖ = 1) {s t : S2 → E3}
    (hs : Topology.IsEmbedding s)
    (ht : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ t)
    (d : OpenPartialHomeomorph E2 S2)
    (A B : OpenPartialHomeomorph (S1 × Real) S2)
    (hB : ContMDiffOn IP (𝓡 2) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 2) IP ∞ B.symm B.target)
    {b ε R : Real} (hε : 0 < ε) (hR : 0 < R)
    (hAs : univ ×ˢ Icc (b - ε) (b + ε) ⊆ A.source)
    (hBs : univ ×ˢ Icc (b - ε) (b + ε) ⊆ B.source)
    (hAh : ∀ q z, z ∈ Icc (b - ε) (b + ε) → inner Real v (s (A (q, z))) = z)
    (hBh : ∀ q z, z ∈ Icc (b - ε) (b + ε) → inner Real v (t (B (q, z))) = z)
    (hboundary : range (fun q : S1 => B (q, b)) = d '' sphere (0 : E2) 1)
    (hinside : ∀ q z, z ∈ Ioo (b - ε) b → B (q, z) ∈ d '' ball (0 : E2) 1)
    (hrim : range (fun q : S1 => s (A (q, b))) =
      range (fun q : S1 => t (B (q, b))))
    {U : Set E3} (hU : IsOpen U)
    (hrimU : range (fun q : S1 => s (A (q, b))) ⊆ U)
    (hgerm : range s ∩ U = range t ∩ U) :
    ∃ r δ : Real, 0 < r ∧ r < R ∧ 0 < δ ∧ δ < r ∧ δ < ε ∧
      ∃ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∃ C : OpenPartialHomeomorph (S1 × Real) S2,
        (∀ x, inner Real v (Q x) = inner Real v x) ∧
        (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - b| ≤ R} ∧
          ∀ x ∉ K, Q x = x) ∧
        EqOn Q id {x | inner Real v x = b} ∧
        C.source = univ ×ˢ Ioo (-r) r ∧
        (∀ q z, C (q, z) = B (q, b + z)) ∧
        (∀ q z, z ∈ Ioo (-r) r →
          Q (t (C (q, z))) = (b + z) • v +
            ((Hemisphere.Plane v).orthogonalProjectionOnto (t (B (q, b))) : E3)) ∧
        range (fun q : S1 => C (q, 0)) = d '' sphere (0 : E2) 1 ∧
        (∀ q z, z ∈ Ioo (-r) 0 → C (q, z) ∈ d '' ball (0 : E2) 1) ∧
        ∀ z ∈ Icc (b - δ) (b + δ),
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (Q (s (A (q, z))))) =
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (s (A (q, b)))) := by
  obtain ⟨η, hη, hηε, hslices⟩ := exists_equal_physical_slices_of_surface_germ
    hs ht.isEmbedding A B (inner Real v) hε hAs hBs hAh hBh hrim hU hrimU hgerm
  obtain ⟨r, hr, hrR, Q, C, hQheight, hsupport, hcentral,
    hCs, hCcyl, hCrim, hCinside, hC⟩ :=
    exists_model_cylindrical_preparation hv ht d B hB hBi hε hR hBs hBh hboundary hinside
  let δ := min η r / 2
  have hδ : 0 < δ := half_pos (lt_min hη hr)
  have hδη : δ < η := by dsimp [δ]; linarith [min_le_left η r]
  have hδr : δ < r := by dsimp [δ]; linarith [min_le_right η r]
  refine ⟨r, δ, hr, hrR, hδ, hδr, hδη.trans hηε, Q, C, hQheight,
    hsupport, hcentral, hCs, hC, hCcyl, hCrim, hCinside, ?_⟩
  intro z hz
  have hzη : z ∈ Icc (b - η) (b + η) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hzr : z - b ∈ Ioo (-r) r := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hmotion (q : S1) : Q (t (B (q, z))) = z • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto (t (B (q, b))) : E3) := by
    have hh := hCcyl q (z - b) hzr
    rw [hC] at hh
    simpa only [add_sub_cancel] using hh
  have hprojection (q : S1) : (Hemisphere.Plane v).orthogonalProjectionOnto
      (Q (t (B (q, z)))) =
      (Hemisphere.Plane v).orthogonalProjectionOnto (t (B (q, b))) := by
    rw [hmotion]
    exact congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply
      (z, (Hemisphere.Plane v).orthogonalProjectionOnto (t (B (q, b)))))
  calc
    _ = (fun x => (Hemisphere.Plane v).orthogonalProjectionOnto (Q x)) ''
        range (fun q : S1 => s (A (q, z))) := range_comp _ _
    _ = (fun x => (Hemisphere.Plane v).orthogonalProjectionOnto (Q x)) ''
        range (fun q : S1 => t (B (q, z))) := by rw [hslices z hzη]
    _ = range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (t (B (q, b)))) := by
      rw [← range_comp]
      exact congrArg Set.range (funext hprojection)
    _ = _ := by
      have hh := congrArg (fun S : Set E3 => (Hemisphere.Plane v).orthogonalProjectionOnto '' S) hrim
      rw [← range_comp, ← range_comp] at hh
      exact hh.symm

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
