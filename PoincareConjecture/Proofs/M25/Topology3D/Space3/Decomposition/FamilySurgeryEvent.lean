import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.CompactHeightGap
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyTubeOwnership
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.RetainedCapPlacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularSurgeryFromTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_family_surgery_event
    (hP : PlanarSchoenfliesService) (P : SurgeryCapProfile)
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3)
    (hembed : ∀ i : Fin n, IsCollarEmbedding (psi i))
    (hdisjoint : Pairwise (fun i j : Fin n =>
      Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
        (range (fun q : UnitTwoSphere => psi j (q, 0)))))
    (u : UnitTwoSphere) (t d : ℝ) (hd : 0 < d)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hsmooth : ContDiffOn ℝ ∞ T T.source)
    (hinverse : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p : E2 × ℝ, ⟪(u : E3), T p⟫_ℝ = p.2)
    (hwhole : ∀ x ∈ closedBall (0 : E2) 1,
      ∀ z ∈ Ioo (t - d) (t + d),
        T (x, z) ∈ (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))) ↔
          x ∈ sphere (0 : E2) 1) :
    ∃ j : Fin n, ∃ E : RegularSurgeryEvent (psi j) u,
      E.cutHeight = t ∧ E.data.width = d ∧ E.data.tube = T ∧ E.profile = P ∧
      (∀ i : Fin n, i ≠ j → ∀ k : Fin 2,
        Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
          (range (fun q : UnitTwoSphere => E.child k (q, 0)))) := by
  obtain ⟨j, _howner, _hunique, hsingle, hothers⟩ :=
    exists_family_tube_owner n psi hembed hdisjoint t d hd T hsource hwhole
  obtain ⟨D, hDw, hDT⟩ := exists_regular_surgery_data_of_tube hP
    (psi j) (hembed j) u t d hd T hsource hsmooth hinverse hheight hsingle
  obtain ⟨E, hcut, hdata, hprofile⟩ :=
    exists_regular_surgery_event P (psi j) (hembed j) u t D
  have hprojections : E.data.width = D.width ∧ E.data.tube = D.tube := by
    cases hcut
    have heq : E.data = D := eq_of_heq hdata
    exact ⟨congrArg (fun X => X.width) heq, congrArg (fun X => X.tube) heq⟩
  have hwidth : E.data.width = d := hprojections.1.trans hDw
  have htube : E.data.tube = T := hprojections.2.trans hDT
  obtain ⟨_hdelta, _hc, hck, hkw, _hl, _hlM⟩ := E.parameter_bounds
  have hcap (k : Fin 2) : (E.newCap k).cap ⊆
      T '' (closedBall (0 : E2) 1 ×ˢ Ioo (t - d) (t + d)) := by
    intro y hy
    have hbound := ((E.newCap k).cap_abs_height_bounds y hy).2
    obtain ⟨_hp, hT, hct, hremoval, _hscale, _hsign⟩ := E.newCap_spec k
    have hsmall : (E.newCap k).removal < d := by
      rw [hremoval, ← hwidth]
      exact hck.trans hkw
    have hyheight : |⟪(u : E3), y⟫_ℝ - t| < d := by
      rw [hct, hcut] at hbound
      exact hbound.trans_lt hsmall
    rw [(E.newCap k).cap_eq_image] at hy
    obtain ⟨q, _hq, heq⟩ := hy
    let p : E2 × ℝ := (((E.newCap k).profile.model q).1,
      (E.newCap k).cutHeight + (E.newCap k).sign *
        ((E.newCap k).removal + (E.newCap k).scale *
          ((E.newCap k).profile.model q).2))
    have hpy : T p = y := by
      change (E.newCap k).tube p = y at heq
      rwa [hT, htube] at heq
    have hheightp : |p.2 - t| < d := by
      rw [← hheight p, hpy]
      exact hyheight
    refine ⟨p, ⟨?_, ?_⟩, hpy⟩
    · exact mem_closedBall_zero_iff.mpr ((E.newCap k).profile.model_fst_norm_le q)
    · obtain ⟨hlo, hhi⟩ := abs_lt.mp hheightp
      exact ⟨by linarith only [hlo], by linarith only [hhi]⟩
  have hzero (f : UnitTwoSphere × ℝ → E3) :
      f '' (univ ×ˢ ({0} : Set ℝ)) = range (fun q : UnitTwoSphere => f (q, 0)) := by
    ext y
    constructor
    · rintro ⟨⟨q, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  obtain ⟨_hparent, _hannulus, _hcores, hchildren, _hseams, _hdis⟩ := E.region_identities
  refine ⟨j, E, hcut, hwidth, htube, hprofile, ?_⟩
  intro i hij k
  rw [← hzero (E.child k), hchildren k]
  apply disjoint_union_right.mpr
  constructor
  · apply (hdisjoint hij).mono_right
    rintro y ⟨q, _hq, rfl⟩
    exact mem_range_self q
  · exact (hothers i hij).mono_right (hcap k)


theorem exists_family_surgery_event_avoiding
    (hP : PlanarSchoenfliesService) (P : SurgeryCapProfile)
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3)
    (hembed : ∀ i : Fin n, IsCollarEmbedding (psi i))
    (hdisjoint : Pairwise (fun i j : Fin n =>
      Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
        (range (fun q : UnitTwoSphere => psi j (q, 0)))))
    (u : UnitTwoSphere) (t d : ℝ) (hd : 0 < d)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hsmooth : ContDiffOn ℝ ∞ T T.source)
    (hinverse : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p : E2 × ℝ, ⟪(u : E3), T p⟫_ℝ = p.2)
    (hwhole : ∀ x ∈ closedBall (0 : E2) 1,
      ∀ z ∈ Ioo (t - d) (t + d),
        T (x, z) ∈ (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))) ↔
          x ∈ sphere (0 : E2) 1)
    (K : Set E3) (hK : IsCompact K)
    (hmiss : ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ≠ t) :
    ∃ j : Fin n, ∃ E : RegularSurgeryEvent (psi j) u,
      E.cutHeight = t ∧ E.data.width < d ∧ E.data.tube = T ∧ E.profile = P ∧
      (∀ y ∈ K, E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|) ∧
      (∀ i : Fin n, i ≠ j → ∀ k : Fin 2,
        Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
          (range (fun q : UnitTwoSphere => E.child k (q, 0)))) := by
  obtain ⟨w, hw, hwd, hgap⟩ := exists_compact_height_gap K hK u t d hd hmiss
  have hband : Ioo (t - w) (t + w) ⊆ Ioo (t - d) (t + d) := by
    intro z hz
    exact ⟨by linarith only [hz.1, hwd], by linarith only [hz.2, hwd]⟩
  obtain ⟨j, E, hcut, hwidth, htube, hprofile, hothers⟩ :=
    exists_family_surgery_event hP P n psi hembed hdisjoint u t w hw T
      hsource hsmooth hinverse hheight (fun x hx z hz => hwhole x hx z (hband hz))
  refine ⟨j, E, hcut, ?_, htube, hprofile, ?_, hothers⟩
  · rw [hwidth]
    exact hwd
  · intro y hy
    rw [hwidth, hcut]
    exact hgap y hy

end PoincareConjecture.M25.Topology3D
