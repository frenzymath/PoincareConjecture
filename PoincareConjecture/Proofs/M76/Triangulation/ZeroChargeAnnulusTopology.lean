import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalSegments
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundedRegions
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}





theorem polygon_collar_annulus_topology
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P) (hdim : Module.finrank ℝ F = 2)
    {f : E × ℝ → F} {r R : ℝ} (hR : 0 < R) (hRr : R < r)
    (hf : FinitePiecewiseAffineOn f (P.boundary ℝ ×ˢ Icc (-r) r))
    (hinj : InjOn f (P.boundary ℝ ×ˢ Icc (-r) r)) :
    IsCompact (f '' (P.boundary ℝ ×ˢ Icc (-R) R)) ∧
      interior (f '' (P.boundary ℝ ×ˢ Icc (-R) R)) =
        f '' (P.boundary ℝ ×ˢ Ioo (-R) R) ∧
      frontier (f '' (P.boundary ℝ ×ˢ Icc (-R) R)) =
        f '' (P.boundary ℝ ×ˢ ({-R, R} : Set ℝ)) ∧
      IsConnected (interior (f '' (P.boundary ℝ ×ˢ Icc (-R) R))) := by
  let N := f '' (P.boundary ℝ ×ˢ Icc (-R) R)
  have hsub : P.boundary ℝ ×ˢ Icc (-R) R ⊆ P.boundary ℝ ×ˢ Icc (-r) r :=
    prod_mono Subset.rfl (fun _ hz => ⟨(by linarith [hz.1]), by linarith [hz.2]⟩)
  have hNc : IsCompact N := (P.isCompact_boundary.prod isCompact_Icc).image_of_continuousOn
    (hf.continuousOn.mono hsub)
  have hmodel : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ F := by
    simp [Module.finrank_prod, hdim]
  have hinside : f '' (P.boundary ℝ ×ˢ Ioo (-R) R) ⊆ interior N := by
    rintro _ ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    obtain ⟨u, v, hux, hvx, huv, hUsub, _⟩ := P.exists_local_segment_pair hP hPinj hx
    let U := segment ℝ x u ∪ segment ℝ x v
    have hU : IsFinitePLBallPair ℝ U {u, v} := by
      have h := isFinitePLBallPair_two_segments hux hvx.symm
        (by simpa only [segment_symm ℝ u x] using huv)
      simpa only [segment_symm ℝ u x] using h
    have hxU : x ∈ U := Or.inl (left_mem_segment ℝ x u)
    have hprod := hU.prod (isFinitePLBallPair_Icc (by linarith : -R < R))
    have hUS : U ×ˢ Icc (-R) R ⊆ P.boundary ℝ ×ˢ Icc (-r) r :=
      (prod_mono hUsub Subset.rfl).trans hsub
    have hb := hprod.image_of_subset hf hUS hinj
    have hpoint : f (x, z) ∈ interior (f '' (U ×ˢ Icc (-R) R)) := by
      rw [hb.interior_eq_sdiff_of_finrank_eq hmodel]
      refine ⟨⟨(x, z), ⟨hxU, hz.1.le, hz.2.le⟩, rfl⟩, ?_⟩
      rintro ⟨p, hp, heq⟩
      have hpU := hprod.1 hp
      have hpx : p = (x, z) := hinj (hUS hpU) (hUS ⟨hxU, hz.1.le, hz.2.le⟩) heq
      subst p
      rcases hp with hp | hp
      · rcases hp.1 with hx | hx
        · exact hux hx.symm
        · exact hvx hx.symm
      · rcases hp.2 with hz' | hz'
        · exact hz.1.ne hz'.symm
        · exact hz.2.ne hz'
    exact interior_mono (image_mono (prod_mono hUsub Subset.rfl)) hpoint
  have houtside (x : E) (hx : x ∈ P.boundary ℝ) (z : ℝ)
      (hz : z ∈ Icc (-r) r) (hzR : z ∉ Icc (-R) R) : f (x, z) ∉ N := by
    rintro ⟨p, hp, heq⟩
    have hpz : p = (x, z) := hinj (hsub hp) ⟨hx, hz⟩ heq
    exact hzR (hpz ▸ hp).2
  have hrim (x : E) (hx : x ∈ P.boundary ℝ) (z : ℝ)
      (hz : z ∈ ({-R, R} : Set ℝ)) : f (x, z) ∉ interior N := by
    have hnot : f (x, z) ∈ closure Nᶜ := by
      rcases hz with hz | hz
      · subst z
        have hsmall : P.boundary ℝ ×ˢ Ioo (-r) (-R) ⊆ P.boundary ℝ ×ˢ Icc (-r) r := by
          rintro ⟨y, t⟩ ⟨hy, ht⟩
          exact ⟨hy, ht.1.le, by linarith [ht.2]⟩
        have hc := (hf.continuousOn (x, -R) (show (x, -R) ∈ P.boundary ℝ ×ˢ Icc (-r) r
          from ⟨hx, by constructor <;> linarith⟩)).mono hsmall
        apply hc.mem_closure
        · rw [closure_prod_eq, closure_Ioo (by linarith : -r ≠ -R)]
          exact ⟨subset_closure hx, by constructor <;> linarith⟩
        · rintro ⟨y, t⟩ ⟨hy, ht⟩
          exact houtside y hy t (hsmall ⟨hy, ht⟩).2 (fun h => (not_lt_of_ge h.1) ht.2)
      · subst z
        have hsmall : P.boundary ℝ ×ˢ Ioo R r ⊆ P.boundary ℝ ×ˢ Icc (-r) r := by
          rintro ⟨y, t⟩ ⟨hy, ht⟩
          exact ⟨hy, by linarith [ht.1], ht.2.le⟩
        have hc := (hf.continuousOn (x, R) (show (x, R) ∈ P.boundary ℝ ×ˢ Icc (-r) r
          from ⟨hx, by constructor <;> linarith⟩)).mono hsmall
        apply hc.mem_closure
        · rw [closure_prod_eq, closure_Ioo hRr.ne]
          exact ⟨subset_closure hx, le_rfl, hRr.le⟩
        · rintro ⟨y, t⟩ ⟨hy, ht⟩
          exact houtside y hy t (hsmall ⟨hy, ht⟩).2 (fun h => (not_lt_of_ge h.2) ht.1)
    simpa only [closure_compl, mem_compl_iff] using hnot
  have hint : interior N = f '' (P.boundary ℝ ×ˢ Ioo (-R) R) := by
    apply Subset.antisymm _ hinside
    intro y hy
    obtain ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩ := interior_subset hy
    refine ⟨(x, z), ⟨hx, ?_⟩, rfl⟩
    have hzrim : z ∉ ({-R, R} : Set ℝ) := fun h => hrim x hx z h hy
    have hzn : z ≠ -R := fun h => hzrim (Or.inl h)
    have hzp : z ≠ R := fun h => hzrim (Or.inr h)
    exact ⟨lt_of_le_of_ne hz.1 hzn.symm, lt_of_le_of_ne hz.2 hzp⟩
  have hfront : frontier N = f '' (P.boundary ℝ ×ˢ ({-R, R} : Set ℝ)) := by
    rw [frontier, hNc.isClosed.closure_eq]
    apply Subset.antisymm
    · rintro y ⟨hy, hyn⟩
      obtain ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩ := hy
      refine ⟨(x, z), ⟨hx, ?_⟩, rfl⟩
      by_contra h
      have hzn : z ≠ -R := fun he => h (Or.inl he)
      have hzp : z ≠ R := fun he => h (Or.inr he)
      exact hyn (hinside ⟨(x, z), ⟨hx, lt_of_le_of_ne hz.1 hzn.symm,
        lt_of_le_of_ne hz.2 hzp⟩, rfl⟩)
    · rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
      refine ⟨⟨(x, z), ⟨hx, ?_⟩, rfl⟩, hrim x hx z hz⟩
      change z = -R ∨ z = R at hz
      rcases hz with hz | hz <;> subst z <;> constructor <;> linarith
  have hconn : IsConnected (P.boundary ℝ) := by
    obtain ⟨e⟩ := P.nonempty_boundary_homeomorph_circle hP hPinj
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  refine ⟨hNc, hint, hfront, ?_⟩
  rw [hint]
  exact (hconn.prod (isConnected_Ioo (by linarith : -R < R))).image f
    (hf.continuousOn.mono ((prod_mono Subset.rfl Ioo_subset_Icc_self).trans hsub))

end PoincareConjecture.M76.ZeroChargeJoint
