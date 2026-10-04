import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoordinateHalfBoxes
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLSubsets
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineLevelComplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineSlabComplex

/-!
# The whole original surface band from its actual product collar

Cut the original finite source triangulation by zero transverse
coordinate and the height bounds. The same product restricts to
the complete surface band; affine projection removes only the
zero coordinate. See Alexander 1924, pp. 6--8, Hudson 1969,
pp. 12--19 and M76 derivation 286ax.
-/

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite PL collar covering the complete surface band
restricts to a finite PL product of its unchanged core and
the full closed height interval. Its values remain exactly
those of the original zero-transverse product, including at
both endpoints. See Alexander pp. 6--8 and derivation 286ax. -/
theorem IsFinitePL.exists_original_surface_band_product
    {B : Set E} {T S : Set F} {r δ c : ℝ} (hr : 0 < r) (hδ : δ ∈ Icc 0 r)
    {G : (B ×ˢ base r : Set (E × (ℝ × ℝ))) ≃ₜ T} (hG : G.IsFinitePL)
    (A : F → ℝ)
    (hheight : ∀ p, A (G p) = c + (p : E × (ℝ × ℝ)).2.1)
    (hsurface : ∀ p, (G p : F) ∈ S ↔ (p : E × (ℝ × ℝ)).2.2 = 0)
    (hband : S ∩ {x | |A x - c| ≤ δ} ⊆ T) :
    ∃ C : (B ×ˢ Icc (-δ) δ : Set (E × ℝ)) ≃ₜ (S ∩ {x | |A x - c| ≤ δ} : Set F),
      C.IsFinitePL ∧ (∀ p, A (C p) = c + (p : E × ℝ).2) ∧
      ∀ p : (B ×ˢ Icc (-δ) δ : Set (E × ℝ)),
        (C p : F) = G ⟨((p : E × ℝ).1, ((p : E × ℝ).2, 0)),
        ⟨p.property.1,
          ⟨(neg_le_neg hδ.2).trans p.property.2.1, p.property.2.2.trans hδ.2⟩,
          neg_nonpos.mpr hr.le, hr.le⟩⟩ := by
  let U : Set (E × (ℝ × ℝ)) :=
    ((B ×ˢ base r) ∩ {x | x.2.2 = 0}) ∩ {x | x.2.1 ∈ Icc (-δ) δ}
  let z : (E × (ℝ × ℝ)) →ₗ[ℝ] ℝ :=
    (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ E (ℝ × ℝ))
  let u : (E × (ℝ × ℝ)) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ E (ℝ × ℝ))
  have hcopy := hG
  obtain ⟨_, ⟨K, hK, hKS, _⟩, _⟩ := hcopy
  obtain ⟨J, hJ, hJS⟩ := K.exists_finite_affineLevel_complex hK z.toAffineMap 0
  rw [hKS] at hJS
  obtain ⟨Q, hQ, hQU⟩ := J.exists_finite_affineSlab_complex hJ u.toAffineMap (-δ) δ
  rw [hJS] at hQU
  change Q.space = U at hQU
  have hUS : U ⊆ B ×ˢ base r := fun _ hx => hx.1.1
  have hmem (x : (B ×ˢ base r : Set (E × (ℝ × ℝ)))) :
      (x : E × (ℝ × ℝ)) ∈ U ↔ (G x : F) ∈ S ∩ {y | |A y - c| ≤ δ} := by
    constructor
    · intro hx
      refine ⟨(hsurface x).mpr hx.1.2, ?_⟩
      change |A (G x) - c| ≤ δ
      rw [hheight, add_sub_cancel_left]
      exact abs_le.mpr hx.2
    · intro hx
      refine ⟨⟨x.property, (hsurface x).mp hx.1⟩, ?_⟩
      have hh := hx.2
      change |A (G x) - c| ≤ δ at hh
      rw [hheight, add_sub_cancel_left] at hh
      exact abs_le.mp hh
  let H := G.restrictSubsets hUS hband hmem
  have hH : H.IsFinitePL := hG.restrictSubsets hUS hband hmem Q hQ hQU
  let p : (E × (ℝ × ℝ)) →L[ℝ] (E × ℝ) :=
    (ContinuousLinearMap.fst ℝ E (ℝ × ℝ)).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E (ℝ × ℝ)))
  have hp : FinitePiecewiseAffineOn p U :=
    ⟨Q, hQ, hQU, Q.affineOnFaces_affine p.toContinuousAffineMap⟩
  have hpinj : InjOn p U := by
    intro x hx y hy hxy
    have hbase : x.1 = y.1 := congrArg (fun q : E × ℝ => q.1) hxy
    have htime : x.2.1 = y.2.1 := congrArg (fun q : E × ℝ => q.2) hxy
    exact Prod.ext hbase (Prod.ext htime (hx.1.2.trans hy.1.2.symm))
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hI : Icc (-δ) δ ⊆ Icc (-r) r := fun _ hx =>
    ⟨(neg_le_neg hδ.2).trans hx.1, hx.2.trans hδ.2⟩
  have hpimage : p '' U = B ×ˢ Icc (-δ) δ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.1.1.1, hx.2⟩
    · intro hy
      refine ⟨(y.1, (y.2, 0)), ⟨⟨⟨hy.1, hI hy.2, hzero⟩, rfl⟩, hy.2⟩, rfl⟩
  obtain ⟨b, hb, hbval⟩ := hp.exists_homeomorph_image hpinj
  let a := (Homeomorph.setCongr hpimage.symm).trans
    (b.symm.trans (Homeomorph.setCongr rfl))
  have ha : a.IsFinitePL := hb.symm.setCongr hpimage rfl
  let C := a.trans H
  have hvalue (q : (B ×ˢ Icc (-δ) δ : Set (E × ℝ))) :
      (C q : F) = G ⟨((q : E × ℝ).1, ((q : E × ℝ).2, 0)),
        ⟨q.property.1, hI q.property.2, hzero⟩⟩ := by
    have hpq : p (a q) = (q : E × ℝ) := by
      change p (b.symm ⟨q, hpimage.symm.subset q.property⟩) = (q : E × ℝ)
      rw [← hbval, b.apply_symm_apply]
    have hbase : (a q : E × (ℝ × ℝ)).1 = (q : E × ℝ).1 :=
      congrArg (fun w : E × ℝ => w.1) hpq
    have htime : (a q : E × (ℝ × ℝ)).2.1 = (q : E × ℝ).2 :=
      congrArg (fun w : E × ℝ => w.2) hpq
    have hpoint : (a q : E × (ℝ × ℝ)) =
        ((q : E × ℝ).1, ((q : E × ℝ).2, 0)) :=
      Prod.ext hbase (Prod.ext htime (a q).property.1.2)
    change (G ⟨a q, hUS (a q).property⟩ : F) = _
    exact congrArg (fun x : (B ×ˢ base r : Set (E × (ℝ × ℝ))) => (G x : F))
      (Subtype.ext hpoint)
  refine ⟨C, ha.trans hH, ?_, hvalue⟩
  intro q
  rw [hvalue, hheight]

end Homeomorph
