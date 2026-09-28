import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.IdentityAnnulus

set_option autoImplicit false

open Set Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

theorem identity_resolving_strip_images_disjoint
    {X : Type*} {L d b : ℝ} (hb : 0 < b) (hbd : b ≤ d)
    (τ : ((ℝ × ℝ) × ℝ) → X)
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔
        z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) :
    Disjoint (τ '' (strip b true '' rectangle (4 * L) d))
      (τ '' (strip b false '' rectangle (4 * L) d)) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨_, ⟨p, hp, rfl⟩, hpy⟩ ⟨_, ⟨q, hq, rfl⟩, hqy⟩
  have h := ((hfib _ (identity_strip_mapsTo hbd true hp)
    _ (identity_strip_mapsTo hbd false hq)).mp (hpy.trans hqy.symm)).1
  have hh := congrArg Prod.snd h
  change max |p.2| b = -max |q.2| b at hh
  linarith [le_max_right |p.2| b, le_max_right |q.2| b]

theorem exists_identity_resolving_annulus_pair
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (τ : ((ℝ × ℝ) × ℝ) → X)
    (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔
        z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) :
    ∃ g : Bool → (ℝ × ℝ) → X,
      (∀ positive,
        Topology.IsEmbedding (fun x : squareAnnulus L d => g positive x) ∧
        PolyhedralPLInCharts e (g positive) (squareAnnulus L d) ∧
        (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
          g positive (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
            τ ((u, signedHeight b positive u), s)) ∧
        g positive '' squareAnnulus L d = τ '' (strip b positive '' rectangle (4 * L) d) ∧
        squareAnnulus L d ∩ g positive ⁻¹' (τ '' identityTubeSide L d) =
          frontier (squareAnnulus L d) ∧
        Disjoint (g positive '' squareAnnulus L d) (τ '' identityTubeAxis L d)) ∧
      Disjoint (g true '' squareAnnulus L d) (g false '' squareAnnulus L d) := by
  classical
  choose a E g h using fun positive =>
    exists_identity_resolving_annulus e hcompat hd hwidth hb hbd positive τ hτ hfib
  refine ⟨g, ?_, ?_⟩
  · intro positive
    obtain ⟨_, hgemb, hgPL, hE, hgE, hperiod, himage, _, _, _, haxis, hfront⟩ := h positive
    refine ⟨hgemb, hgPL, ?_, himage, hfront, haxis⟩
    intro s hs u
    rw [← hE ((s : AddCircle (4 * L)), u), hgE]
    exact hperiod s hs u
  · have htrue := (h true).2.2.2.2.2.2.1
    have hfalse := (h false).2.2.2.2.2.2.1
    rw [htrue, hfalse]
    exact identity_resolving_strip_images_disjoint hb hbd.le τ hfib

end Dehn
