import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares









set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

local notation "P2" => (ℝ × ℝ)

theorem isPreconnected_squareAnnulus_sdiff_depth {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (side : Bool) :
    IsPreconnected (squareAnnulus L d \ {p | depth L p = if side then d else -d}) := by
  let J : Set ℝ := if side then Ico (-d) d else Ioc (-d) d
  have hJ (u : ℝ) : u ∈ J ↔ u ∈ Icc (-d) d ∧ u ≠ if side then d else -d := by
    cases side
    · change (-d < u ∧ u ≤ d) ↔ (-d ≤ u ∧ u ≤ d) ∧ u ≠ -d
      exact ⟨fun h => ⟨⟨h.1.le, h.2⟩, h.1.ne'⟩,
        fun h => ⟨lt_of_le_of_ne h.1.1 h.2.symm, h.1.2⟩⟩
    · change (-d ≤ u ∧ u < d) ↔ (-d ≤ u ∧ u ≤ d) ∧ u ≠ d
      exact ⟨fun h => ⟨⟨h.1, h.2.le⟩, h.2.ne⟩,
        fun h => ⟨h.1.1, lt_of_le_of_ne h.1.2 h.2⟩⟩
  have hJcv : Convex ℝ J := by
    cases side
    · exact convex_Ioc _ _
    · exact convex_Ico _ _
  have hsub : Icc (0 : ℝ) (4 * L) ×ˢ J ⊆ rectangle (4 * L) d :=
    fun _ hx => ⟨hx.1, (hJ _).mp hx.2 |>.1⟩
  have hdepth (p : P2) (hp : p ∈ rectangle (4 * L) d) :
      depth L (wrappedStripMap L p) = p.2 := by
    have ht : 4 * |p.2| < L := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
    rw [← annulusMap_coe (by linarith) ht hp.1]
    exact depth_annulusMap (by linarith) ht _
  have himage : wrappedStripMap L '' (Icc (0 : ℝ) (4 * L) ×ˢ J) =
      squareAnnulus L d \ {p | depth L p = if side then d else -d} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨mem_squareAnnulus_iff_depth.mpr ?_, ?_⟩
      · rw [hdepth q (hsub hq)]
        exact (hJ q.2).mp hq.2 |>.1
      · change depth L (wrappedStripMap L q) ≠ _
        rw [hdepth q (hsub hq)]
        exact (hJ q.2).mp hq.2 |>.2
    · rintro ⟨hp, hne⟩
      obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth ⟨p, hp⟩
      have hu := mem_squareAnnulus_iff_depth.mp hp
      refine ⟨(s, depth L p), ⟨hs, (hJ _).mpr ⟨hu, hne⟩⟩, ?_⟩
      rw [← annulusMap_coe (by linarith)
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hu) (by norm_num)) hwidth) hs]
      exact hsp.symm
  rw [← himage]
  exact ((convex_Icc _ _).prod hJcv).isPreconnected.image _
    ((finitePiecewiseAffineOn_wrappedStripMap hd hwidth).continuousOn.mono hsub)

theorem isPreconnected_annulus_image_sdiff_boundary {T q : Set P2} {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (side : Bool)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL)
    (hq : ∀ p : squareAnnulus L d, (c p : P2) ∈ q ↔
      depth L p = if side then d else -d) : IsPreconnected (T \ q) := by
  obtain ⟨f, hf, hcf⟩ := hc
  have himage : f '' (squareAnnulus L d \ {p | depth L p = if side then d else -d}) = T \ q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hcf ⟨x, hx.1⟩]
      exact ⟨(c ⟨x, hx.1⟩).property, fun h => hx.2 ((hq ⟨x, hx.1⟩).mp h)⟩
    · rintro ⟨hy, hyq⟩
      let x := c.symm ⟨y, hy⟩
      have hcx : (c x : P2) = y := congrArg Subtype.val (c.apply_symm_apply _)
      refine ⟨x, ⟨x.property, ?_⟩, (hcf x).symm.trans hcx⟩
      intro hx
      exact hyq (hcx ▸ (hq x).mpr hx)
  rw [← himage]
  exact (isPreconnected_squareAnnulus_sdiff_depth hd hwidth side).image _
    (hf.continuousOn.mono sdiff_subset)




theorem polygon_annulus_exists_empty_inside {T : Set P2} {m n : ℕ}
    (P : Polygon P2 (m + 3)) (Q : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPT : P.boundary ℝ ⊆ T) (hQT : Q.boundary ℝ ⊆ T)
    (hdis : Disjoint (P.boundary ℝ) (Q.boundary ℝ))
    (hconnP : IsPreconnected (T \ P.boundary ℝ))
    (hconnQ : IsPreconnected (T \ Q.boundary ℝ)) :
    closure P.inside ∩ T = P.boundary ℝ ∨ closure Q.inside ∩ T = Q.boundary ℝ := by
  have hsideP : T \ P.boundary ℝ ⊆ P.inside ∨ T \ P.boundary ℝ ⊆ P.outside := by
    apply hconnP.subset_or_subset (P.isOpen_inside hP hinjP)
      (P.isOpen_outside hP hinjP) P.disjoint_inside_outside
    rw [← P.compl_boundary_eq_inside_union_outside]
    exact sdiff_subset_compl _ _
  have hsideQ : T \ Q.boundary ℝ ⊆ Q.inside ∨ T \ Q.boundary ℝ ⊆ Q.outside := by
    apply hconnQ.subset_or_subset (Q.isOpen_inside hQ hinjQ)
      (Q.isOpen_outside hQ hinjQ) Q.disjoint_inside_outside
    rw [← Q.compl_boundary_eq_inside_union_outside]
    exact sdiff_subset_compl _ _
  have hcapP (h : T \ P.boundary ℝ ⊆ P.outside) :
      closure P.inside ∩ T = P.boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxT⟩
      by_contra hxb
      rw [P.closure_inside hP hinjP] at hx
      exact hx (h ⟨hxT, hxb⟩)
    · intro x hx
      exact ⟨(P.isFinitePLBallPair_closed_inside hP hinjP).1 hx, hPT hx⟩
  have hcapQ (h : T \ Q.boundary ℝ ⊆ Q.outside) :
      closure Q.inside ∩ T = Q.boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxT⟩
      by_contra hxb
      rw [Q.closure_inside hQ hinjQ] at hx
      exact hx (h ⟨hxT, hxb⟩)
    · intro x hx
      exact ⟨(Q.isFinitePLBallPair_closed_inside hQ hinjQ).1 hx, hQT hx⟩
  rcases hsideP with hpin | hpout
  · rcases hsideQ with hqin | hqout
    · have hQP : Q.boundary ℝ ⊆ P.inside := fun x hx =>
        hpin ⟨hQT hx, fun hp => Set.disjoint_left.mp hdis hp hx⟩
      have hnest := P.closure_inside_subset_inside_of_boundary_subset_inside Q
        hP hinjP hQ hinjQ hQP
      obtain ⟨x, hx⟩ := (P.isConnected_boundary hP hinjP).nonempty
      have hxQ := hqin ⟨hPT hx, Set.disjoint_left.mp hdis hx⟩
      exact ((hnest (subset_closure hxQ)).1 hx).elim
    · exact Or.inr (hcapQ hqout)
  · exact Or.inl (hcapP hpout)

end Dehn
