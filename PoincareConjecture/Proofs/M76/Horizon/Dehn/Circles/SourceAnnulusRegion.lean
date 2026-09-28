import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSides

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

local notation "P2" => (ℝ × ℝ)

private theorem polygon_annulus_region_of_inner_depth
    {T : Set P2} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    {m n : ℕ} (P : Polygon P2 (m + 3)) (Q : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hdis : Disjoint (P.boundary ℝ) (Q.boundary ℝ))
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL)
    (hinner : ∀ p : squareAnnulus L d, (c p : P2) ∈ P.boundary ℝ ↔ depth L p = d)
    (houter : ∀ p : squareAnnulus L d, (c p : P2) ∈ Q.boundary ℝ ↔ depth L p = -d)
    (hQT : Q.boundary ℝ ⊆ T)
    (hcap : closure P.inside ∩ T = P.boundary ℝ) :
    closure P.inside ⊆ Q.inside ∧ T = closure Q.inside \ P.inside := by
  obtain ⟨hcover, hseam, hrim⟩ := annulusSquare_partition (L := L) hd
  have hball : IsFinitePLBallPair P2 (annulusSquare L d ∪ squareAnnulus L d)
      (frontier (annulusSquare L (-d))) :=
    hcover.symm ▸ isFinitePLBallPair_annulusSquare (by linarith : 2 * -d < L)
  obtain ⟨f, hf, hcf⟩ := hc
  have hmem (p : squareAnnulus L d) :
      (p : P2) ∈ frontier (annulusSquare L d) ↔ (c p : P2) ∈ P.boundary ℝ :=
    (mem_frontier_annulusSquare_iff L d p).trans (hinner p).symm
  have himage : f '' frontier (annulusSquare L (-d)) = Q.boundary ℝ := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hcf ⟨p, hrim hp⟩]
      exact (houter ⟨p, hrim hp⟩).mpr
        ((mem_frontier_annulusSquare_iff L (-d) p).mp hp)
    · intro hy
      let p := c.symm ⟨y, hQT hy⟩
      have hcp : (c p : P2) = y := congrArg Subtype.val (c.apply_symm_apply _)
      refine ⟨p, ?_, (hcf p).symm.trans hcp⟩
      exact (mem_frontier_annulusSquare_iff L (-d) p).mpr
        ((houter p).mp (hcp.symm ▸ hy))
  exact polygon_annulus_region_of_cap hball
    (isFinitePLBallPair_annulusSquare (by linarith : 2 * d < L)) hseam hrim
    P Q hP hinjP hQ hinjQ hdis c ⟨f, hf, hcf⟩ hmem hcap hcf himage

theorem exists_polygon_collar_of_square_annulus
    {T : Set P2} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL) :
    ∃ (m n : ℕ) (P : Polygon P2 (m + 3)) (I : Polygon P2 (n + 3)) (reverse : Bool),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
      I.HasSimplicialEdges ∧ Function.Injective I ∧
      closure I.inside ⊆ P.inside ∧ T = closure P.inside \ I.inside ∧
      (∀ p : squareAnnulus L d, (c p : P2) ∈ P.boundary ℝ ↔
        depth L p = if reverse then d else -d) ∧
      (∀ p : squareAnnulus L d, (c p : P2) ∈ I.boundary ℝ ↔
        depth L p = if reverse then -d else d) ∧
      ∃ e : squareAnnulus L d ≃ₜ ↥(closure P.inside \ I.inside),
        e.IsFinitePL ∧ e.symm.IsFinitePL ∧ ∀ p, (e p : P2) = c p := by
  obtain ⟨m, P, hP, hinjP, hPT, hinner⟩ :=
    exists_polygon_square_annulus_boundary hd hwidth (Or.inr rfl) c hc
  obtain ⟨n, Q, hQ, hinjQ, hQT, houter⟩ :=
    exists_polygon_square_annulus_boundary hd hwidth (Or.inl rfl) c hc
  have hdis : Disjoint (P.boundary ℝ) (Q.boundary ℝ) := by
    apply Set.disjoint_left.mpr
    intro x hxP hxQ
    let p := c.symm ⟨x, hPT hxP⟩
    have hcp : (c p : P2) = x := congrArg Subtype.val (c.apply_symm_apply _)
    have hi := (hinner p).mp (hcp.symm ▸ hxP)
    have ho := (houter p).mp (hcp.symm ▸ hxQ)
    linarith
  have hcap := polygon_annulus_exists_empty_inside P Q hP hinjP hQ hinjQ hPT hQT hdis
    (isPreconnected_annulus_image_sdiff_boundary hd hwidth true c hc hinner)
    (isPreconnected_annulus_image_sdiff_boundary hd hwidth false c hc houter)
  have htransport {U : Set P2} (heq : T = U) :
      ∃ e : squareAnnulus L d ≃ₜ U,
        e.IsFinitePL ∧ e.symm.IsFinitePL ∧ ∀ p, (e p : P2) = c p := by
    let e := c.trans (Homeomorph.setCongr heq)
    have he : e.IsFinitePL := by
      obtain ⟨f, hf, hcf⟩ := hc
      exact ⟨f, hf, hcf⟩
    exact ⟨e, he, he.symm, fun _ => rfl⟩
  rcases hcap with hcap | hcap
  · obtain ⟨hnest, hregion⟩ := polygon_annulus_region_of_inner_depth hd hwidth
      P Q hP hinjP hQ hinjQ hdis c hc hinner houter hQT hcap
    exact ⟨n, m, Q, P, false, hQ, hinjQ, hP, hinjP, hnest, hregion,
      houter, hinner, htransport hregion⟩
  · obtain ⟨r, hr, hrdepth, _⟩ := exists_square_annulus_depth_reflection hd hwidth
    let c' := r.trans c
    have hi (p : squareAnnulus L d) : (c' p : P2) ∈ Q.boundary ℝ ↔ depth L p = d := by
      change (c (r p) : P2) ∈ Q.boundary ℝ ↔ _
      rw [houter, hrdepth]
      exact neg_inj
    have ho (p : squareAnnulus L d) : (c' p : P2) ∈ P.boundary ℝ ↔ depth L p = -d := by
      change (c (r p) : P2) ∈ P.boundary ℝ ↔ _
      rw [hinner, hrdepth]
      exact neg_eq_iff_eq_neg
    obtain ⟨hnest, hregion⟩ := polygon_annulus_region_of_inner_depth hd hwidth
      Q P hQ hinjQ hP hinjP hdis.symm c' (hr.trans hc) hi ho hPT hcap
    exact ⟨m, n, P, Q, true, hP, hinjP, hQ, hinjQ, hnest, hregion,
      hinner, houter, htransport hregion⟩

theorem exists_polygon_collar_of_square_annulus_in_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a : E ≃L[ℝ] P2) {T : Set E} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL) :
    ∃ (m n : ℕ) (P : Polygon E (m + 3)) (I : Polygon E (n + 3)) (reverse : Bool),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
      I.HasSimplicialEdges ∧ Function.Injective I ∧
      closure I.inside ⊆ P.inside ∧ T = closure P.inside \ I.inside ∧
      (∀ p : squareAnnulus L d, (c p : E) ∈ P.boundary ℝ ↔
        depth L p = if reverse then d else -d) ∧
      (∀ p : squareAnnulus L d, (c p : E) ∈ I.boundary ℝ ↔
        depth L p = if reverse then -d else d) ∧
      ∃ e : squareAnnulus L d ≃ₜ ↥(closure P.inside \ I.inside),
        e.IsFinitePL ∧ e.symm.IsFinitePL ∧ ∀ p, (e p : E) = c p := by
  obtain ⟨f, hf, hcf⟩ := hc
  have hfi : InjOn f (squareAnnulus L d) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (c.injective (Subtype.ext
      ((hcf ⟨x, hx⟩).trans (hxy.trans (hcf ⟨y, hy⟩).symm))))
  have hfc : f '' squareAnnulus L d = T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hcf ⟨x, hx⟩]
      exact (c ⟨x, hx⟩).property
    · intro hy
      refine ⟨c.symm ⟨y, hy⟩, (c.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hcf, c.apply_symm_apply]
  have hg : FinitePiecewiseAffineOn (a ∘ f) (squareAnnulus L d) :=
    hf.postcomp a.toContinuousLinearMap.toContinuousAffineMap
  obtain ⟨b, hb, hbf⟩ := hg.exists_homeomorph_image (fun x hx y hy heq =>
    hfi hx hy (a.injective heq))
  have him : (a ∘ f) '' squareAnnulus L d = a '' T := by rw [image_comp, hfc]
  let b' := b.trans (Homeomorph.setCongr him)
  have hb' : b'.IsFinitePL := by
    obtain ⟨g, hg, hbg⟩ := hb
    exact ⟨g, hg, hbg⟩
  have hbc (p : squareAnnulus L d) : (b' p : P2) = a (c p) :=
    (hbf p).trans (congrArg a (hcf p).symm)
  obtain ⟨m, n, P, I, reverse, hP, hPi, hI, hIi, hnest, hregion, hout, hin, _⟩ :=
    exists_polygon_collar_of_square_annulus hd hwidth b' hb'
  let P' := P.affineImage a.symm.toLinearEquiv.toAffineEquiv.toAffineMap
  let I' := I.affineImage a.symm.toLinearEquiv.toAffineEquiv.toAffineMap
  have hp := P.affineImage_of_leftInvOn hP hPi
    a.symm.toLinearEquiv.toAffineEquiv.toAffineMap a.toLinearEquiv.toAffineEquiv.toAffineMap
    (fun _ _ => a.apply_symm_apply _)
  have hi := I.affineImage_of_leftInvOn hI hIi
    a.symm.toLinearEquiv.toAffineEquiv.toAffineMap a.toLinearEquiv.toAffineEquiv.toAffineMap
    (fun _ _ => a.apply_symm_apply _)
  have hPcl : closure P'.inside = a.symm '' closure P.inside := P.closure_inside_linearImage a.symm
  have hIcl : closure I'.inside = a.symm '' closure I.inside := I.closure_inside_linearImage a.symm
  have hPin : P'.inside = a.symm '' P.inside := P.inside_linearImage a.symm
  have hIin : I'.inside = a.symm '' I.inside := I.inside_linearImage a.symm
  have hn : closure I'.inside ⊆ P'.inside := by
    rw [hIcl, hPin]
    exact image_mono hnest
  have hreg : T = closure P'.inside \ I'.inside := by
    rw [hPcl, hIin, ← image_sdiff a.symm.injective, ← hregion]
    simp only [image_image, a.symm_apply_apply, image_id']
  have hPb (x : E) : x ∈ P'.boundary ℝ ↔ a x ∈ P.boundary ℝ := by
    rw [Polygon.affineImage_boundary]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change a (a.symm y) ∈ P.boundary ℝ
      simpa only [a.apply_symm_apply] using hy
    · intro hx
      exact ⟨a x, hx, a.symm_apply_apply x⟩
  have hIb (x : E) : x ∈ I'.boundary ℝ ↔ a x ∈ I.boundary ℝ := by
    rw [Polygon.affineImage_boundary]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change a (a.symm y) ∈ I.boundary ℝ
      simpa only [a.apply_symm_apply] using hy
    · intro hx
      exact ⟨a x, hx, a.symm_apply_apply x⟩
  refine ⟨m, n, P', I', reverse, hp.2.1, hp.1, hi.2.1, hi.1, hn, hreg, ?_, ?_, ?_⟩
  · intro p
    rw [hPb, ← hbc]
    exact hout p
  · intro p
    rw [hIb, ← hbc]
    exact hin p
  · let e := c.trans (Homeomorph.setCongr hreg)
    have he : e.IsFinitePL := ⟨f, hf, hcf⟩
    exact ⟨e, he, he.symm, fun _ => rfl⟩

end Dehn
