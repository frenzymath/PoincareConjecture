import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Containment
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ThroughPoint
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.AnnularRegion

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : ConnectedSpace S1 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem exists_lower_annular_end
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) (hclosed : IsClosed C)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {a b : Real} (hab : a < b)
    (hlower : ∀ p ∈ C, a ≤ h p)
    (hgreater : ∃ p ∈ C, b < h p)
    (hregular : ∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) (hDb : D.center < b) :
    D.scale < 0 ∧
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, D.center)) = D.chart '' sphere (0 : E2) 1 ∧
      F '' (univ ×ˢ Icc D.center b) ⊆ C ∧
      F '' (univ ×ˢ Ioo D.center b) ⊆ interior C ∧
      (∀ q t, t ∈ Icc D.center b → inner Real v (g (F (q, t))) = t) ∧
      ∀ p ∈ D.chart '' sphere (0 : E2) 1,
        F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p := by
  have hboundary : D.chart '' sphere (0 : E2) 1 ⊆ C := fun p hp =>
    ((core_inter_closed_disk L hpair hcore D hD).superset hp).1
  have hDheight : ∀ p ∈ D.chart '' sphere (0 : E2) 1, h p = D.center :=
    fun p hp => ((hgerm p (hboundary hp)).eq_of_nhds).trans (D.height_eq_on_boundary p hp)
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr zero_le_one
  let p := D.chart x
  have hp : p ∈ D.chart '' sphere (0 : E2) 1 := mem_image_of_mem _ hx
  have hDa : a ≤ D.center := by rw [← hDheight p hp]; exact hlower p (hboundary hp)
  have hpband : h p ∈ Icc a b := by rw [hDheight p hp]; exact ⟨hDa, hDb.le⟩
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, hband, hpF⟩ :=
    exists_smooth_regular_band_component_through_point hh hab hregular p hpband
  have hsub : univ ×ˢ Icc a b ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hFs ▸ ⟨mem_univ _, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have htarget : F '' (univ ×ˢ Icc a b) ⊆ F.target := by
    rintro y ⟨z, hz, rfl⟩
    exact F.map_source (hsub hz)
  obtain ⟨hs, hretained, hinterior⟩ := upper_closed_strip_subset_core L hpair hcore hC hclosed
    hh.continuous hgerm F (by linarith : a - δ < a) (by linarith : b < b + δ)
      hFs hheight hlower hgreater D hD hDa hDb hp (htarget hpF)
  have hconn : IsPreconnected (D.chart '' sphere (0 : E2) 1) :=
    (isConnected_sphere (E := E2) (by simp [← Module.finrank_eq_rank, E2])
      0 zero_le_one).isPreconnected.image _
        (D.chart.continuousOn.mono (sphere_subset_closedBall.trans D.source))
  have hboundaryband : D.chart '' sphere (0 : E2) 1 ⊆ h ⁻¹' Icc a b := by
    intro z hz
    change h z ∈ Icc a b
    rw [hDheight z hz]
    exact ⟨hDa, hDb.le⟩
  have hboundaryF : D.chart '' sphere (0 : E2) 1 ⊆ F '' (univ ×ˢ Icc a b) := by
    rw [hband]
    exact hconn.subset_connectedComponentIn hp hboundaryband
  have hcircle := D.boundary_eq_annular_slice F hFs hF hFi hheight
    (show D.center ∈ Ioo (a - δ) (b + δ) from ⟨by linarith, by linarith⟩)
    (hboundaryF.trans htarget) hDheight
  refine ⟨hs, δ, hδ, F, hFs, hF, hFi, hheight, hcircle.symm, hretained, hinterior, ?_, ?_⟩
  · intro q t ht
    have hqC := hretained (mem_image_of_mem F (show (q, t) ∈ univ ×ˢ Icc D.center b from
      ⟨mem_univ _, ht⟩))
    exact ((hgerm _ hqC).eq_of_nhds).symm.trans
      (hheight q t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  · intro z hz
    exact hband.trans (connectedComponentIn_eq (hband ▸ hboundaryF hz))

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
